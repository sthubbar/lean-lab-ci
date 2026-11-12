#!/usr/bin/env python3
"""TACTIC SWEEP, a free proving lane with no AI. Written by lrefresh 20261112 with Steve live, 11:00 PM PT Wed 11-11.
Runs on the public mirror sthubbar/lean-lab-ci in .github/workflows/tactic-sweep.yml, one matrix shard per job.
Kept in scripts/ci/ of the Lean Lab folder; ci_mirror.py deploys it to the mirror beside the workflow files.
  sweep.py list N                          print every candidate file and its shard
  sweep.py shard I N OUTDIR RUNID          sweep shard I of N and write OUTDIR/RUNID-I.json
  sweep.py push LOCALFILE REPOPATH         commit one file to branch sweep-results with git plumbing, retried on a race
  sweep.py summary RUNID OUTDIR            read every RUNID-*.json on sweep-results, write the run summary and push it
Per file of the shard: find sorry sites in theorem and lemma declarations of two kinds, a tactic block that is only
sorry and := sorry; lake build the file's LeanLab imports; compile the file as it is to get its declaration uses sorry
warnings; compile a temp copy where each site is one first combinator of ten tactics, each tagged by a trace and ending
in sorry; a declaration is closed when its sorry warning is gone, it has no error and every site in it names a tactic;
then compile a final copy with each site set to that single tactic and keep only declarations still closed there.
Never changes a statement: only the sorry token is replaced. Never writes native_decide, exact? or apply?.
Skips any file over 3000 lines and any compile over 10 minutes. Paths containing /old/ are never read."""
import hashlib, json, os, re, signal, subprocess, sys, tempfile, time
SRC = "LeanLab/LeanLab"
TACTICS = ["norm_num", "simp", "decide", "omega", "linarith", "nlinarith", "positivity", "aesop", "field_simp", "ring"]
BANNED = ("native_decide", "exact?", "apply?")
MAX_LINES, COMPILE_MAX = 3000, 600
DEADLINE = int(os.environ.get("SWEEP_DEADLINE", "12000"))  # no new file after 200 min: one file can take 60 min of imports and 3 compiles of 10, inside the 300 min job
IMPORT_MAX = int(os.environ.get("SWEEP_IMPORT_MAX", "3600"))
# MEMORY CAP, lrefresh 20261112: test run 43158278442 lost its runner to a shutdown signal, exit 143, 15 min into the sweep, the same
# death the nightly saw; a hosted runner has 16 GB. Every lake and lean call runs in its own process group and is killed above this.
MEM_MB = int(os.environ.get("SWEEP_MEM_MB", "11000"))
T0 = time.time()
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|example|structure|class|inductive|opaque|axiom)\b\s*([^\s:(\[{]*)")
def say(s): print(s, flush=True)
def shard_of(p, n): return int(hashlib.sha1(p.encode()).hexdigest(), 16) % n
def lean_files():
    out = []
    for dp, dn, fn in os.walk(SRC):
        dn[:] = sorted(d for d in dn if d not in ("old", "build", ".lake"))
        for f in sorted(fn):
            p = os.path.join(dp, f).replace(os.sep, "/")
            if f.endswith(".lean") and "/old/" not in p: out.append(p)
    return out
def mask(lines):
    """the code of each line with comments blanked, same length, so columns stay valid"""
    out, depth = [], 0
    for l in lines:
        r, i = [], 0
        while i < len(l):
            two = l[i:i + 2]
            if depth:
                if two == "/-": depth += 1; r.append("  "); i += 2; continue
                if two == "-/": depth -= 1; r.append("  "); i += 2; continue
                r.append(" "); i += 1; continue
            if two == "/-": depth = 1; r.append("  "); i += 2; continue
            if two == "--": r.append(" " * (len(l) - i)); break
            r.append(l[i]); i += 1
        out.append("".join(r))
    return out
def decls(code):
    return [(i, m.group(1), m.group(2) or f"example@{i + 1}") for i, l in enumerate(code) for m in [DECL.match(l)] if m]
def owner(ds, i):
    k = None
    for d in ds:
        if d[0] <= i: k = d
        else: break
    return k
def dec_range(ds, d, n):
    nxt = [x[0] for x in ds if x[0] > d[0]]
    return d[0], (nxt[0] - 1 if nxt else n - 1)
def indent(s): return len(s) - len(s.lstrip())
def sites(lines):
    """candidate sorry sites: dict line index to (col, kind, declaration start), first candidate of a line only"""
    code = mask(lines); ds = decls(code); out = {}
    for i, l in enumerate(code):
        for m in re.finditer(r"\bsorry\b", l):
            d = owner(ds, i)
            if not d or d[1] not in ("theorem", "lemma") or i == d[0] and ":=" not in l[:m.start()]: continue
            before, after = l[:m.start()], l[m.end():].strip()
            if after not in ("", ")"): continue
            kind = None
            if re.search(r":=\s*$", before): kind = "term"
            elif re.search(r"\bby\s*$", before): kind = "by"
            elif not before.strip():
                j = i - 1
                while j >= 0 and not code[j].strip(): j -= 1
                k = i + 1
                while k < len(code) and not code[k].strip(): k += 1
                ends = k >= len(code) or indent(code[k]) < indent(l)
                if j >= 0 and ends and re.search(r"\bby\s*$", code[j]): kind = "block"
                elif j >= 0 and ends and re.search(r":=\s*$", code[j]): kind = "term"
            if kind: out[i] = (m.start(), kind, d); break
    return out, ds
def combinator():
    alts = " | ".join(f'({t}; done; trace "SWEEP_OK {t}")' for t in TACTICS)
    return f"set_option maxHeartbeats 200000 in first | {alts} | sorry"
def put(line, col, kind, tac):
    return line[:col] + ("by " if kind == "term" else "") + tac + line[col + 5:]
def group_rss_mb(pg):
    tot = 0
    for d in os.listdir("/proc"):
        if not d.isdigit(): continue
        try: s = open(f"/proc/{d}/stat").read(); f = s[s.rfind(")") + 2:].split()
        except OSError: continue
        if int(f[2]) == pg: tot += int(f[21])
    return tot * os.sysconf("SC_PAGE_SIZE") >> 20
PEAK = [0]
def run_capped(cmd, limit):
    """return code, stdout and the reason it was killed: timeout, memory or empty"""
    with tempfile.TemporaryFile() as fo, tempfile.TemporaryFile() as fe:
        p = subprocess.Popen(cmd, cwd="LeanLab", stdout=fo, stderr=fe, start_new_session=True); t0 = time.time(); why = ""
        while p.poll() is None:
            time.sleep(1); mb = group_rss_mb(p.pid); PEAK[0] = max(PEAK[0], mb)
            if mb > MEM_MB: why = f"memory {mb} MB"
            elif time.time() - t0 > limit: why = "timeout"
            if why:
                try: os.killpg(p.pid, signal.SIGKILL)
                except OSError: pass
                p.wait(); break
        fo.seek(0); fe.seek(0)
        return p.returncode, fo.read().decode("utf-8", "replace"), fe.read().decode("utf-8", "replace"), why
def compile_(path):
    """messages of lake env lean on one file as line, severity and text triples, or None after the 10 minute cap or the memory cap"""
    rc, so, se, why = run_capped(["lake", "env", "lean", "--json", os.path.abspath(path)], COMPILE_MAX)
    if why: say(f"SWEEP KILLED compile of {os.path.basename(path)}: {why}"); return None
    msgs = []
    for l in so.splitlines():
        l = l.strip()
        if l.startswith("{"):
            try: j = json.loads(l)
            except ValueError: continue
            msgs.append(((j.get("pos") or {}).get("line", 0), j.get("severity", ""), j.get("data", "")))
        else:
            m = re.match(r".*?:(\d+):\d+: (error|warning|info)?:?\s*(.*)", l)
            if m: msgs.append((int(m.group(1)), m.group(2) or "information", m.group(3)))
    if rc and not msgs: msgs.append((0, "error", (se or so or "lean failed")[-300:]))
    return msgs
SORRY = re.compile(r"declaration uses .sorry")
def warned(msgs, ds):
    return {owner(ds, ln - 1)[0] for ln, sv, tx in msgs if sv == "warning" and SORRY.search(tx) and owner(ds, ln - 1)}
def errs_in(msgs, lo, hi): return [tx for ln, sv, tx in msgs if sv == "error" and lo + 1 <= ln <= hi + 1]
def build_imports(lines):
    mods = sorted({m.group(1) for l in lines for m in [re.match(r"^\s*import\s+(LeanLab\.\S+)", l)] if m})
    if not mods: return True, "no LeanLab imports"
    rc, so, se, why = run_capped(["lake", "build"] + mods, IMPORT_MAX)
    if why: return False, f"import build killed, {why}"
    return rc == 0, " ".join([l for l in so.splitlines() if "error" in l][:2])[:300]
def sweep_file(path, tmp):
    lines = open(path, encoding="utf-8").read().split("\n")
    if len(lines) > MAX_LINES: return [], f"SKIP over {MAX_LINES} lines"
    S, ds = sites(lines)
    if not S: return [], "no candidate sites"
    ok, why = build_imports(lines)
    if not ok: return [], f"SKIP imports failed: {why}"
    base = compile_(path)
    if base is None: return [], "SKIP base compile over 10 minutes or the memory cap"
    W0 = warned(base, ds); S = {i: s for i, s in S.items() if s[2][0] in W0}
    if not S: return [], "no sorry warning at any site"
    os.makedirs(tmp, exist_ok=True); cp = os.path.join(tmp, "Sweep_" + re.sub(r"\W", "_", path) + ".lean")
    trial = list(lines)
    for i, (c, k, d) in S.items(): trial[i] = put(lines[i], c, k, combinator())
    open(cp, "w", encoding="utf-8").write("\n".join(trial))
    m1 = compile_(cp)
    if m1 is None: return [], "SKIP combinator compile over 10 minutes or the memory cap"
    W1 = warned(m1, ds); ok_at = {}
    for ln, sv, tx in m1:
        q = re.search(r"SWEEP_OK (\S+)", tx)
        if q and ln - 1 in S and ln - 1 not in ok_at: ok_at[ln - 1] = q.group(1)
    closed = set()
    for d in {s[2] for s in S.values()}:
        lo, hi = dec_range(ds, d, len(lines)); mine = [i for i, s in S.items() if s[2] == d]
        if d[0] not in W1 and not errs_in(m1, lo, hi) and all(i in ok_at for i in mine): closed.add(d)
    e1 = [tx for ln, sv, tx in m1 if sv == "error"]
    diag = f", {len(ok_at)} of {len(S)} sites named a tactic, {len(e1)} errors" + (f", first: {' '.join(e1[0].split())[:160]}" if e1 else "")
    for _ in range(2):
        if not closed: return [], f"0 closed of {len({s[2] for s in S.values()})} declarations" + diag
        fin = list(lines)
        for i, (c, k, d) in S.items():
            if d in closed: fin[i] = put(lines[i], c, k, ok_at[i])
        open(cp, "w", encoding="utf-8").write("\n".join(fin))
        m2 = compile_(cp)
        if m2 is None: return [], "SKIP final compile over 10 minutes or the memory cap"
        W2 = warned(m2, ds)
        bad = {d for d in closed if d[0] in W2 or errs_in(m2, *dec_range(ds, d, len(lines)))}
        if not bad: break
        closed -= bad
    else: return [], "final copy kept failing"
    items = []
    for i, (c, k, d) in sorted(S.items()):
        if d not in closed: continue
        new = fin[i]
        if any(b in new for b in BANNED): continue
        items.append({"folder": path.split("/")[2], "file": path, "declaration": d[2], "tactic": ok_at[i], "line": i + 1, "old": lines[i], "new": new})
    return items, f"{len(closed)} closed"
SELFTEST = """import Mathlib.Tactic

theorem sweep_selftest_a : (2 : ℕ) + 2 = 4 := by
  sorry

theorem sweep_selftest_b (x : ℝ) (h : 0 < x) : 0 < x ^ 2 + x := by sorry

theorem sweep_selftest_c : ∀ n : ℕ, n + 0 = n := sorry

theorem sweep_selftest_open (n : ℕ) : n = n + 1 := by
  sorry
"""
def selftest(outdir):
    """proves the machinery on a known file: a, b and c must close, open must not"""
    d = os.path.join(SRC, "SweepSelfTest"); os.makedirs(d, exist_ok=True); p = f"{SRC}/SweepSelfTest/SelfTest.lean"
    open(p, "w", encoding="utf-8").write(SELFTEST)
    try: got, why = sweep_file(p, os.path.join(outdir, "tmp"))
    except Exception as e: got, why = [], f"ERROR {type(e).__name__}: {str(e)[:200]}"
    names = sorted({x["declaration"] + " by " + x["tactic"] for x in got})
    ok = {x["declaration"] for x in got} == {"sweep_selftest_a", "sweep_selftest_b", "sweep_selftest_c"}
    say(f"SWEEP SELFTEST {'OK' if ok else 'FAIL'}: {why}; closed {names}")
    return {"ok": ok, "why": why, "closed": names}
def candidates(n):
    out = []
    for p in lean_files():
        try: t = open(p, encoding="utf-8").read()
        except OSError: continue
        if "sorry" in t: out.append((p, shard_of(p, n)))
    return out
ST = {}
def write(i, n, outdir, run, sha, mine, items, per):
    summ = {"files": len(mine), "declarations_closed": len({(x["file"], x["declaration"]) for x in items}), "sites": len(items),
            "skipped": sum(1 for x in per if x["result"].startswith(("SKIP", "UNFINISHED", "ERROR"))), "seconds": int(time.time() - T0)}
    res = {"run_id": run, "shard": i, "shards": n, "mirror_sha": sha, "items": items, "files": per, "summary": summ, "selftest": ST.get("selftest")}
    f = os.path.join(outdir, f"{run}-{i}.json"); json.dump(res, open(f, "w"), indent=1)
    return f, summ
def shard(i, n, outdir, run):
    os.makedirs(outdir, exist_ok=True); sha = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    mine = [p for p, s in candidates(n) if s == i]; items, per = [], []
    say(f"SWEEP SHARD {i} of {n}: {len(mine)} files with sorry, mirror {sha[:10]}")
    ST["selftest"] = selftest(outdir); last = time.time()
    for p in mine:
        if time.time() - last > 1200 and items:  # push the partial result every 20 min, so even a dead runner leaves its finds
            f0, _ = write(i, n, outdir, run, sha, mine, items, per); push(f0, f"results/{run}-{i}.json", f"tactic sweep partial {run}-{i}"); last = time.time()
        write(i, n, outdir, run, sha, mine, items, per)  # partial result on disk after every file, so a killed job still commits what it found
        if time.time() - T0 > DEADLINE: per.append({"file": p, "result": "UNFINISHED deadline"}); continue
        s = time.time(); PEAK[0] = 0
        try: got, why = sweep_file(p, os.path.join(outdir, "tmp"))
        except Exception as e: got, why = [], f"ERROR {type(e).__name__}: {str(e)[:200]}"
        items += got; per.append({"file": p, "result": why, "seconds": int(time.time() - s)})
        say(f"SWEEP {p}: {why}, {int(time.time() - s)} s, peak {PEAK[0]} MB" + "".join(f"\nSWEEP CLOSED {x['declaration']} line {x['line']} by {x['tactic']}" for x in got))
    f, summ = write(i, n, outdir, run, sha, mine, items, per)
    say(f"SWEEP RESULT shard {i}: {summ['declarations_closed']} declarations closed, {summ['sites']} sites, {summ['files']} files, {summ['skipped']} skipped")
    return f
def git(*a, env=None, inp=None):
    p = subprocess.run(["git", *a], capture_output=True, text=True, env=dict(os.environ, **(env or {})), input=inp)
    return p.returncode, p.stdout.strip()
def push(local, repo_path, msg=None):
    who = {"GIT_AUTHOR_NAME": "tactic-sweep", "GIT_AUTHOR_EMAIL": "lean-merge@users.noreply.github.com",
           "GIT_COMMITTER_NAME": "tactic-sweep", "GIT_COMMITTER_EMAIL": "lean-merge@users.noreply.github.com"}
    idx = {"GIT_INDEX_FILE": os.path.join(os.environ.get("RUNNER_TEMP", "/tmp"), "sweep-push.idx")}
    for k in range(8):
        rc, _ = git("fetch", "-q", "--depth", "1", "origin", "+refs/heads/sweep-results:refs/remotes/origin/sweep-results")
        parent = git("rev-parse", "-q", "--verify", "refs/remotes/origin/sweep-results")[1] if rc == 0 else ""
        git("read-tree", parent, env=idx) if parent else git("read-tree", "--empty", env=idx)
        blob = git("hash-object", "-w", local)[1]
        git("update-index", "--add", "--cacheinfo", f"100644,{blob},{repo_path}", env=idx)
        tree = git("write-tree", env=idx)[1]
        c = git("commit-tree", tree, *(["-p", parent] if parent else []), "-m", msg or f"tactic sweep {repo_path}", env=who)[1]
        if parent:
            n = git("diff-tree", "--no-commit-id", "--name-only", "-r", parent, c)[1].split()
            if not n: say(f"SWEEP PUSH unchanged {repo_path}"); return 0
            if n != [repo_path]: say(f"SWEEP PUSH REFUSED, diff is {n[:5]}"); return 1
        if git("push", "-q", "origin", f"{c}:refs/heads/sweep-results")[0] == 0: say(f"SWEEP PUSHED {repo_path} {c[:10]}"); return 0
        time.sleep(5 + 7 * k + int(hashlib.sha1(repo_path.encode()).hexdigest(), 16) % 9)
    say("SWEEP PUSH FAILED " + repo_path); return 1
def summary(run, outdir):
    os.makedirs(outdir, exist_ok=True)
    if git("fetch", "-q", "--depth", "1", "origin", "+refs/heads/sweep-results:refs/remotes/origin/sweep-results")[0]:
        say("SWEEP SUMMARY no sweep-results branch yet"); return 0
    names = [x for x in git("ls-tree", "--name-only", "refs/remotes/origin/sweep-results", "results/")[1].split() if re.match(rf"results/{run}-\d+\.json$", x)]
    tot = {"run_id": run, "shards_reported": 0, "files": 0, "declarations_closed": 0, "sites": 0, "skipped": 0, "closed": []}
    for nm in sorted(names):
        try: j = json.loads(git("show", f"refs/remotes/origin/sweep-results:{nm}")[1])
        except ValueError: continue
        tot["shards_reported"] += 1
        for k in ("files", "declarations_closed", "sites", "skipped"): tot[k] += j["summary"].get(k, 0)
        tot["closed"] += sorted({f"{x['file']} {x['declaration']} by {x['tactic']}" for x in j["items"]})
    f = os.path.join(outdir, f"{run}-summary.json"); json.dump(tot, open(f, "w"), indent=1)
    say(f"SWEEP RUN {run}: {tot['shards_reported']} shards reported, {tot['declarations_closed']} declarations closed, {tot['sites']} sites, {tot['files']} files, {tot['skipped']} skipped")
    for c in tot["closed"]: say("- " + c)
    if not tot["shards_reported"]: return 0
    return push(f, f"results/{run}-summary.json", f"tactic sweep summary {run}")
if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["list"]:
        for p, s in candidates(int(a[1])): say(f"{s}\t{p}")
    elif a[:1] == ["shard"]: shard(int(a[1]), int(a[2]), a[3], a[4])
    elif a[:1] == ["push"]: sys.exit(push(a[1], a[2]))
    elif a[:1] == ["summary"]: sys.exit(summary(a[1], a[2]))
    else: print(__doc__)

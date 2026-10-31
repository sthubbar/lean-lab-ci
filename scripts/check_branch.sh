#!/bin/bash
# Lean Lab self-check, run by every agent before it publishes a branch.
# Usage: bash scripts/check_branch.sh <Folder>[,<Folder2>] <TAG>
#   Two folders joined by a comma are checked together, added 2026-10-22 by lean-jules for Steve: the old version treated "A,B" as one folder.
#   <Folder> is the folder under LeanLab/LeanLab, for example Ternary78
#   <TAG> is the agent and task, for example GEMINI-task01 or CODEX-task09
# Writes LeanLab/LeanLab/<Folder>/build/<TAG>-CHECK.txt and prints PASS or FAIL.
# Added 2026-10-21 by Steve with Claude, so reviewers read one file instead of redoing the work.
set -uo pipefail
FOLDER="${1:?folder}"; TAG="${2:?tag}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
FOLDER=$(echo "$FOLDER" | tr -d " " | sed -E "s#(^|,)(\./)?(LeanLab/)*#\1#g; s#/(,|$)#\1#g"); F1="${FOLDER%%,*}"
OUT="LeanLab/LeanLab/$F1/build/$TAG-CHECK.txt"; mkdir -p "$(dirname "$OUT")"
git fetch -q origin main 2>/dev/null
# CHECK_BASE override, lrefresh 2026-10-29 on lmerge findings 10-24 and 10-25: an audit on a worktree of new main found no
# changed files and passed empty. Audits run: CHECK_BASE=<pre-run main sha> bash scripts/check_branch.sh <Folder> GATE-AUDIT
BASE="${CHECK_BASE:-$(git merge-base HEAD origin/main 2>/dev/null || git merge-base HEAD main 2>/dev/null || echo "")}"
python3 - "$FOLDER" "$TAG" "$BASE" "$OUT" <<'PY'
import subprocess, sys, re, os
folder, tag, base, out = sys.argv[1:5]
prefix = tag.split("-")[0]
R = []; fails = 0
def rep(ok, msg):
    global fails
    if ok is False: fails += 1
    R.append(("PASS " if ok is True else "FAIL " if ok is False else "WARN ") + msg)
def sh(cmd, cwd=None, timeout=3600):
    p = subprocess.run(cmd, shell=True, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr
if not base:
    rep(False, "no merge base with origin/main; run git fetch origin main first"); base = "HEAD~1"
_, files = sh(f"git diff --name-only {base} HEAD"); _, wt = sh("git status --porcelain")
changed = sorted(set(f for f in files.split() if f) | set(l[3:].strip() for l in wt.splitlines() if l[3:].strip())); changed = [f for f in changed if f != out]
mines = tuple(f"LeanLab/LeanLab/{x}/" for x in folder.split(",") if x); mine = mines
outside = [f for f in changed if not f.startswith(mine) and f != "LOG.md"]
rep(not outside, "only your folder and LOG.md changed" + ("" if not outside else ": outside files " + ", ".join(outside)))
binaries = [f for f in changed if re.search(r"\.(pdf|zip|tar|gz|png|jpg|djvu|ps)$", f, re.I)]
rep(not binaries, "no downloads or binaries committed" + ("" if not binaries else ": " + ", ".join(binaries)))
_, st = sh("git status --porcelain"); st = "\n".join(l for l in st.splitlines() if not l.endswith(os.path.basename(out))); rep(not st.strip(), "everything committed" if not st.strip() else "uncommitted changes remain, commit before publishing")
leans = [f for f in changed if f.endswith(".lean") and f.startswith(mine) and os.path.exists(f)]
def sorries(text): return len(re.findall(r"\bsorry\b", re.sub(r"--[^\n]*|/-.*?-/", "", text, flags=re.S)))
before = after = 0
for f in leans:
    after += sorries(open(f).read())
    rc, old = sh(f"git show {base}:{f}"); before += sorries(old) if rc == 0 else 0
# DECOMPOSE rule, Steve live 2026-10-27 via lrefresh: new sorries are allowed only in NEW files and only on
# theorems whose doc comment starts with LEAF; an existing file may never gain a sorry.
new_files = [f for f in leans if sh(f"git cat-file -e {base}:{f}")[0] != 0]
leaf_new = bad_new = 0; bo = ao = 0
for f in leans:
    tx = open(f).read()
    if f in new_files:
        for mm in re.finditer(r"(?:theorem|lemma)\s+\S+", tx):
            nxt_m = re.search(r"\n(?:/--|@\[|theorem |lemma |def |end |namespace |section )", tx[mm.end():])
            body = tx[mm.start(): mm.end() + (nxt_m.start() if nxt_m else len(tx))]
            if not re.search(r"\bsorry\b", re.sub(r"--[^\n]*|/-.*?-/", "", body, flags=re.S)): continue
            doc = tx[max(0, mm.start() - 800):mm.start()]; d = doc.rfind("/--")
            if d != -1 and re.match(r"/--\s*LEAF", doc[d:]): leaf_new += 1
            else: bad_new += 1
    else:
        ao += sorries(tx); rc, old_t = sh(f"git show {base}:{f}"); bo += sorries(old_t) if rc == 0 else 0
rep(ao <= bo and bad_new == 0, f"sorry count in changed files {before} before, {after} after; existing files {bo} to {ao}; new files {leaf_new} LEAF sorries allowed, {bad_new} sorries not marked LEAF")
names = []
for f in leans:
    mod = "LeanLab." + f[len("LeanLab/LeanLab/"):-5].replace("/", ".")
    serial = "LEAN_NUM_THREADS=1 " if os.environ.get("CHECK_SERIAL") == "1" else ""
    rc, log = sh(f"{serial}lake build {mod}", cwd="LeanLab")
    # OOM RETRY, lrefresh 2026-10-29 on lmerge findings: big certificate modules, MuStar55Cert and Akeno2026, were killed
    # with exit 137 on 7 GB. Lake 4.35 has no -j; LEAN_NUM_THREADS=1 builds one module at a time, single-threaded, tested 2026-10-29.
    if rc != 0 and not serial and re.search(r"\b137\b|Killed|out of memory|signal 9|SIGKILL", log):
        rc, log = sh(f"LEAN_NUM_THREADS=1 lake build {mod}", cwd="LeanLab"); log = "OOM retry, serial build. " + log
    rep(rc == 0, f"lake build {mod} exit {rc}" + ("" if rc == 0 else ": " + log.strip().splitlines()[-1][:200] if log.strip() else ""))
    ns = []; text = re.sub(r"/-.*?-/", "", open(f).read(), flags=re.S)
    for line in text.splitlines():
        m = re.match(r"\s*namespace\s+(\S+)", line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r"\s*end\s+(\S+)\s*$", line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)", line)
        if m and not line.lstrip().startswith("private"): names.append((mod, ".".join(ns + [m.group(1)])))
if names:
    mods = sorted(set(m for m, _ in names))
    src = "\n".join(f"import {m}" for m in mods) + "\n" + "\n".join(f"#print axioms {n}" for _, n in names) + "\n"
    open("/tmp/LeanLabAxCheck.lean", "w").write(src)
    rc, ax = sh("lake env lean /tmp/LeanLabAxCheck.lean", cwd="LeanLab")
    ok3 = {"propext", "Classical.choice", "Quot.sound"}
    lines = [l for l in ax.splitlines() if "depends on axioms" in l or "does not depend on any axioms" in l]
    bad = [l for l in lines if "depends on axioms" in l and not set(re.findall(r"[\w.]+", l.split("depends on axioms")[1])) <= ok3]
    rep(len(lines) >= len(names), f"#print axioms ran for {len(lines)} of {len(names)} theorems" + ("" if rc == 0 else f", lean exit {rc}"))
    rep(None if bad else True, "axioms only propext, Classical.choice, Quot.sound" if not bad else f"{len(bad)} theorems use other axioms, label them CONDITIONAL or sorry: " + " | ".join(b.strip()[:160] for b in bad[:8]))
    R.append("AXIOMS\n" + "\n".join(lines))
    stm = any(f in {m + "STATEMENTS.md" for m in mines} for f in changed)
    rep(stm, "STATEMENTS.md updated with twins for new theorems")
rep(any(f in {m + "PROGRESS.md" for m in mines} for f in changed), "PROGRESS.md updated")
_, dl = sh(f"git diff {base} HEAD -- LOG.md")
rep(any(l.startswith("+" + prefix) for l in dl.splitlines()), f"LOG.md has a line starting {prefix}")
prose = [l[1:] for f in changed if f.endswith(".md") for l in sh(f"git diff {base} HEAD -- '{f}'")[1].splitlines() if l.startswith("+") and not l.startswith("+++")]
dash = [l for l in prose if "—" in l or "–" in l]
rep(not dash, "no em or en dashes in added prose" + ("" if not dash else f": {len(dash)} lines"))
summary = ("RESULT PASS" if fails == 0 else f"RESULT FAIL, {fails} failed checks") + f"  {tag}  folder {folder}  base {base[:9]}"
open(out, "w").write(summary + "\n" + "\n".join(R) + "\n"); print(summary); print("\n".join(r for r in R if not r.startswith("AXIOMS")))
PY

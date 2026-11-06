#!/usr/bin/env python3
"""Nightly whole build of main on lean-lab-ci, split by folder across a job matrix. Written lmerge 20261106T1323Z, FOR lmerge from lrefresh 1153Z.
The single job was killed 1.5 to 3 h in every night from 10-28, exit 143, runner shutdown signal, with tail -60 hiding all output, so main had no
whole build, the compiled cache never saved, and a58e8169f broke OpenProblems unseen.
  ci_nightly.py plan N            print the folders of each group
  ci_nightly.py group I N OUTDIR  build group I of N, one lake build per folder, every folder even after a failure; writes OUTDIR/gI.tsv
  ci_nightly.py report DIR N      read every gI.tsv under DIR, print the NIGHTLY verdict, exit 1 on any failed or missing folder
Every result line goes to stdout as it happens, so the job log keeps it even when the runner dies. HEARTBEAT lines record free memory and disk.
"""
import glob, os, re, subprocess, sys, threading, time
LEAN = "LeanLab/LeanLab"
DEADLINE = 19200  # seconds per group, leaves the job limit room to save the cache
def say(s): print(s, flush=True)
def modules():
    out = {}
    for dp, dn, fn in os.walk(LEAN):
        dn[:] = [d for d in dn if d not in ("old", "build", ".lake")]
        for f in fn:
            if not f.endswith(".lean"): continue
            p = os.path.join(dp, f); q = os.path.relpath(p, LEAN).split(os.sep)
            if len(q) < 2: continue
            out.setdefault(q[0], []).append((os.path.getsize(p), "LeanLab." + ".".join(q)[:-5]))
    return out
def plan(n):
    # greedy, largest folder first onto the lightest group; deterministic for one tree, and every job reads the same checkout
    m = modules(); g = [[0, []] for _ in range(n)]
    for f in sorted(m, key=lambda x: (-sum(s for s, _ in m[x]), x)):
        t = min(range(n), key=lambda i: (g[i][0], i)); g[t][0] += sum(s for s, _ in m[f]); g[t][1].append(f)
    return m, [sorted(x[1]) for x in g]
def heartbeat():
    while True:
        time.sleep(300)
        a = re.search(r"MemAvailable:\s+(\d+)", open("/proc/meminfo").read()); d = os.statvfs("/")
        say(f"NIGHTLY HEARTBEAT mem_free_mb {int(a.group(1)) >> 10 if a else -1} disk_free_gb {d.f_bavail * d.f_frsize >> 30} load {os.getloadavg()[0]:.1f}")
def lake(mods, env=None):
    # lake build takes the modules of one folder; no line is hidden except the per-module success lines
    p = subprocess.Popen(["lake", "build"] + mods, cwd="LeanLab", stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace", env=env)
    errs = []
    for l in p.stdout:
        if l.startswith("✔"): continue
        print(l, end="", flush=True)
        if "error:" in l and len(errs) < 3: errs.append(" ".join(l.split())[:200])
    return p.wait(), errs
def group(i, n, out):
    m, g = plan(n); os.makedirs(out, exist_ok=True); t0 = time.time()
    threading.Thread(target=heartbeat, daemon=True).start()
    say(f"NIGHTLY GROUP {i} of {n}: {len(g[i])} folders, {sum(len(m[f]) for f in g[i])} modules")
    with open(os.path.join(out, f"g{i}.tsv"), "w") as w:
        for f in g[i]:
            if time.time() - t0 > DEADLINE:
                say(f"NIGHTLY UNFINISHED {f} deadline"); print(f, "UNFINISHED", "deadline", sep="\t", file=w, flush=True); continue
            s = time.time(); mods = sorted(x for _, x in m[f]); rc, errs = lake(mods)
            if rc in (137, 143, -9, -15):
                say(f"NIGHTLY RETRY {f} serial after rc {rc}")
                rc, errs = lake(mods, dict(os.environ, LEAN_NUM_THREADS="1"))
            v = "OK" if rc == 0 else "FAIL"; why = "; ".join(errs).replace("\t", " ") or f"rc {rc}"
            say(f"NIGHTLY {v} {f} {len(mods)} modules {int(time.time() - s)} s" + ("" if rc == 0 else f": {why}"))
            print(f, v, why if rc else "", sep="\t", file=w, flush=True)
def report(d, n):
    want = {f: gi for gi, fs in enumerate(plan(n)[1]) for f in fs}; seen = {}
    for p in glob.glob(os.path.join(d, "**", "g*.tsv"), recursive=True):
        for l in open(p):
            q = l.rstrip("\n").split("\t"); seen[q[0]] = q[1:] + [""]
    bad = [(f, seen[f][0], seen[f][1]) for f in sorted(seen) if seen[f][0] != "OK"]
    miss = sorted(f for f in want if f not in seen)
    ok = sum(1 for f in seen if seen[f][0] == "OK")
    say(f"NIGHTLY RESULT folders OK {ok}, FAIL or UNFINISHED {len(bad)}, no result {len(miss)}, of {len(want)}")
    for f, v, why in bad: say(f"NIGHTLY {v} {f}: {why}")
    if bad: say(f"NIGHTLY FIRST FAILING FOLDER {bad[0][0]}")
    if miss: say("NIGHTLY NO RESULT, runner died or group cancelled: groups " + ",".join(str(x) for x in sorted({want[f] for f in miss})) + ": " + " ".join(miss)[:400])
    return 1 if bad or miss else 0
if __name__ == "__main__":
    c = sys.argv[1]
    if c == "plan":
        m, g = plan(int(sys.argv[2]))
        for i, fs in enumerate(g): say(f"{i}\t{sum(len(m[f]) for f in fs)}\t{' '.join(fs)}")
    elif c == "group": group(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    elif c == "report": sys.exit(report(sys.argv[2], int(sys.argv[3])))

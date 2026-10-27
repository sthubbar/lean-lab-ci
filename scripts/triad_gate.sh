#!/bin/bash
# Lean Lab triad gate. Run by a Jules triad attempt before it publishes. Written 2026-10-22 by lean-refresh with Steve live.
# Usage: bash scripts/triad_gate.sh <Folder> <NN> <letter>     for example: bash scripts/triad_gate.sh Tolev2009 01 a
# The attempt may only ADD these files, nothing else in the repo:
#   LeanLab/LeanLab/<Folder>/Triad<NN>.lean            must contain theorem triad<NN>_main
#   LeanLab/LeanLab/<Folder>/Triad<NN>/<Any>.lean      optional helper modules
#   LeanLab/LeanLab/<Folder>/Triad<NN>.md              twin, paper page, vacuity instance, MATCH line
#   LeanLab/LeanLab/<Folder>/build/GEMINI-triad<NN><letter>.log and -GATE.txt
# PASS needs: only those paths changed, every new module builds, no banned token, every theorem's axioms within
# propext, Classical.choice, Quot.sound, and triad<NN>_main present. Writes the GATE file and prints RESULT.
set -uo pipefail
F="${1:?folder}"; NN="${2:?nn}"; X="${3:?letter}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"; export PATH="$HOME/.elan/bin:$PATH"
git fetch -q origin main 2>/dev/null
BASE=$(git merge-base HEAD origin/main 2>/dev/null || echo "")
python3 - "$F" "$NN" "$X" "$BASE" <<'PY'
import subprocess, sys, re, os
F, NN, X, base = sys.argv[1:5]
D = f"LeanLab/LeanLab/{F}/"; out = f"{D}build/GEMINI-triad{NN}{X}-GATE.txt"; os.makedirs(D + "build", exist_ok=True)
R = []; fails = 0
def rep(ok, msg):
    global fails
    if not ok: fails += 1
    R.append(("PASS " if ok else "FAIL ") + msg)
def sh(c, cwd=None):
    p = subprocess.run(c, shell=True, cwd=cwd, capture_output=True, text=True, timeout=5400); return p.returncode, p.stdout + p.stderr
ok_path = re.compile(rf"^{re.escape(D)}(Triad{NN}\.lean|Triad{NN}\.md|Triad{NN}/[A-Za-z0-9_]+\.lean|build/GEMINI-triad{NN}{X}(\.log|-GATE\.txt))$")
if not base: rep(False, "no merge base with origin/main"); base = "HEAD~1"
_, a = sh(f"git diff --name-status {base} HEAD"); _, w = sh("git status --porcelain")
ch = [l.split("\t") for l in a.splitlines() if l.strip()]
bad = [p for st, *ps in ch for p in ps if not ok_path.match(p) or st[0] != "A"] + [l[3:] for l in w.splitlines() if l[3:].strip() and not l[3:].strip().endswith("-GATE.txt")]
rep(not bad, "only new Triad files added, nothing else touched" + ("" if not bad else ": " + ", ".join(bad[:12])))
leans = sorted(p for _, *ps in ch for p in ps if p.endswith(".lean") and ok_path.match(p))
main = f"{D}Triad{NN}.lean"
rep(os.path.exists(main), f"{main} exists")
BAN = [r"\bsorry\b", r"\badmit\b", r"native_decide", r"^\s*axiom\b", r"\bnotation\b", r"^\s*(local\s+)?(macro|syntax|elab|macro_rules|infix|infixl|infixr|prefix|postfix)\b",
       r"\bunsafe\b", r"implemented_by", r"@\[extern", r"^\s*opaque\b", r"ofReduceBool", r":\s*Prop\s*:=\s*True\b", r":=\s*True\s*$", r"\bdebug\.skipKernelTC\b"]
names = []
for f in leans:
    t = re.sub(r"/-.*?-/", "", open(f).read(), flags=re.S); t = re.sub(r"--[^\n]*", "", t)
    hits = [b for b in BAN if re.search(b, t, flags=re.M)]
    rep(not hits, f"{f}: no banned tokens" + ("" if not hits else ": " + " ".join(hits)))
    ns = []
    for line in t.splitlines():
        m = re.match(r"\s*namespace\s+(\S+)", line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r"\s*end\s+(\S+)\s*$", line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)", line)
        if m: names.append(("LeanLab." + f[len("LeanLab/LeanLab/"):-5].replace("/", "."), ".".join(ns + [m.group(1)])))
mainn = [n for m, n in names if n.split(".")[-1] == f"triad{NN}_main"]
rep(len(mainn) == 1, f"exactly one theorem triad{NN}_main, found {len(mainn)}")
for f in leans:
    mod = "LeanLab." + f[len("LeanLab/LeanLab/"):-5].replace("/", ".")
    rc, log = sh(f"lake build {mod}", cwd="LeanLab")
    open(f"{D}build/GEMINI-triad{NN}{X}.log", "a").write(f"== lake build {mod} exit {rc}\n{log[-4000:]}\n")
    rep(rc == 0, f"lake build {mod} exit {rc}")
if names:
    src = "\n".join(sorted({f"import {m}" for m, _ in names})) + "\n" + "\n".join(f"#print axioms {n}" for _, n in names) + "\n"
    open("/tmp/TriadAx.lean", "w").write(src)
    rc, ax = sh("lake env lean /tmp/TriadAx.lean", cwd="LeanLab")
    open(f"{D}build/GEMINI-triad{NN}{X}.log", "a").write("== #print axioms\n" + ax + "\n")
    lines = [l for l in ax.splitlines() if "axioms" in l]
    ok3 = {"propext", "Classical.choice", "Quot.sound"}
    badax = [l for l in lines if "depends on axioms" in l and not set(re.findall(r"[\w.]+", l.split("depends on axioms")[1])) <= ok3]
    rep(len(lines) >= len(names) and rc == 0, f"#print axioms ran for {len(lines)} of {len(names)} theorems")
    rep(not badax, "every theorem uses only propext, Classical.choice, Quot.sound" + ("" if not badax else ": " + " | ".join(b.strip()[:140] for b in badax[:6])))
md = f"{D}Triad{NN}.md"
rep(os.path.exists(md) and all(k in open(md).read().upper() for k in ("TWIN", "PAGE", "INSTANCE")), f"{md} has TWIN, PAGE and INSTANCE lines")
res = ("RESULT PASS" if fails == 0 else f"RESULT FAIL, {fails} failed") + f"  triad{NN}{X}  {F}  base {base[:9]}"
open(out, "w").write(res + "\n" + "\n".join(R) + "\n"); print(res); print("\n".join(R))
PY

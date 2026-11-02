#!/usr/bin/env python3
"""Lean Lab VACUITY CHECK, a mutation test. Written 2026-11-01 by lproof for Steve. Warns only, it never rejects.
Question: did a proof close its theorem only because the hypotheses contradict each other?
Method: right after each target theorem a scratch copy of the file gets a twin with the SAME binders and the SAME
proof text and a mutated conclusion, then the scratch file is compiled once. The kernel accepting a twin is a real
proof that the hypotheses are contradictory, so a VACUOUS line cannot be a false alarm about the hypotheses.
  F form   theorem t__vacF <binders> : False := <proof>
  S form   the conclusion keeps its leading forall, exists and arrow skeleton and only the last leaf becomes False,
           needed when the proof starts with intro or an anonymous constructor, as Pintz2021 leaf_main_term_bound_exists_C
The twin sits beside the original, so later theorems still see the true statement and a file costs one compile.
Limit: it tests the PROOF. Contradictory hypotheses that the proof never exploited are not caught, nor is a true but
weakened statement. NOT_FLAGGED means no evidence of vacuity, never a proof of honesty.
Usage, from the repository root, modules the file imports already built, for example after check_branch.sh:
  python3 scripts/vacuity_check.py [BASE]                     theorems the branch closed or added, BASE as seal_check.py
  python3 scripts/vacuity_check.py --file LeanLab/LeanLab/X/Y.lean [--thm NAME ...]   named theorems, or every closed one
  options: --closed-only, skip theorems new on the branch; --timeout SECONDS per file, default 1800; --lean-dir LeanLab
Prints VERDICT <word> <file> <theorem> <detail>, one per theorem, then VACUITY <flagged> flagged of <n>.
Words: VACUOUS, the F form compiled; VACUOUS_ANTECEDENT, the S form compiled; VIA_SORRY, a twin compiled but leans on an
open sorry, so a leaf and these hypotheses clash; NOT_FLAGGED; UNPARSED, skipped rather than guessed; SKIP, conclusion
is already False or nothing to mutate; ERROR, no verdict. Scratch files go in a fresh system temp folder. Exit is 0."""
import re, os, sys, subprocess, tempfile

OPEN, CLOSE = "([{⦃⟨", ")]}⦄⟩"

def sh(c, cwd=None):
    p = subprocess.run(c, shell=True, capture_output=True, cwd=cwd)
    return p.returncode, p.stdout.decode("utf-8", "replace")

def blank(t):
    """Same length as t, comments and strings turned to spaces, newlines kept, so offsets match the raw file."""
    o, i, d, n = list(t), 0, 0, len(t)
    def wipe(a, b):
        for k in range(a, min(b, n)):
            if o[k] != "\n": o[k] = " "
    while i < n:
        if t.startswith("/-", i):
            j, d = i + 2, 1
            while j < n and d:
                if t.startswith("/-", j): d += 1; j += 2
                elif t.startswith("-/", j): d -= 1; j += 2
                else: j += 1
            wipe(i, j); i = j
        elif t.startswith("--", i):
            j = t.find("\n", i); j = n if j == -1 else j; wipe(i, j); i = j
        elif t.startswith("'\"'", i): wipe(i, i + 3); i += 3
        elif t[i] == '"':
            j = i + 1
            while j < n and t[j] != '"': j += 2 if t[j] == "\\" else 1
            wipe(i, j + 1); i = j + 1
        else: i += 1
    return "".join(o)

MODS = r"(?:(?:private|protected|noncomputable|nonrec|public)\s+)*"
THM = re.compile(r"^([ \t]*)((?:(?:open|omit|set_option|include)\b[^\n]*?\bin[ \t]+)?)((?:@\[[^\]]*\]\s*)*)" + MODS + r"(?:theorem|lemma)\s+(\S+)", re.M)
CMD = re.compile(r"^[ \t]*(?:@\[|(?:private|protected|noncomputable|nonrec|public|local|scoped|unsafe|partial)\s|(?:theorem|lemma|def|abbrev|example|instance|structure|class|inductive|axiom|opaque|namespace|section|end|open|variable|universe|attribute|set_option|omit|include|mutual|export|notation|infix|infixl|infixr|prefix|postfix|macro|syntax|elab|initialize|#\w+)\b)", re.M)

def split_sig(b, i):
    """From just after the theorem name: offsets of the type colon and of the := that starts the proof, in blanked text b."""
    d, colon, n = 0, None, len(b)
    while i < n:
        c = b[i]
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        elif d == 0 and colon is None and c == ":" and not b.startswith(":=", i): colon = i
        elif d == 0 and b.startswith(":=", i): return colon, i
        i += 1
    return colon, None

def skeleton(c):
    """Conclusion text with its last leaf replaced by False, or None when no forall, exists or arrow prefix can be peeled safely."""
    pos, peeled = 0, False
    while True:
        s = pos + len(c[pos:]) - len(c[pos:].lstrip())
        if c.startswith(("∀", "∃"), s):
            d = 0
            for j in range(s, len(c)):
                if c[j] in OPEN: d += 1
                elif c[j] in CLOSE: d -= 1
                elif c[j] == "," and d == 0: pos = j + 1; peeled = True; break
            else: return None
            continue
        d, arrow = 0, None
        for j in range(s, len(c)):
            if c[j] in OPEN: d += 1
            elif c[j] in CLOSE: d -= 1
            elif d == 0 and c[j] == "↔": return None
            elif d == 0 and (c[j] == "→" or c.startswith("->", j)):
                arrow = j + (1 if c[j] == "→" else 2); break
        if arrow is None: break
        if re.search(r"(?<![\w'.])(?:fun|match|if|let|have|λ)(?![\w'])", c[s:arrow]): return None
        pos = arrow; peeled = True
    if not peeled: return None
    if c[pos:].lstrip().startswith("¬"): return None
    return c[:pos].rstrip() + " False"

def variables_mentioned(b, upto, text, binders):
    """Names from variable lines still in scope above a theorem that its proof or conclusion mentions and its binders do not
    rebind: dropping the conclusion would otherwise drop them, and include of a closed section's name would be an error."""
    stack, cur = [], []
    for m in re.finditer(r"^[ \t]*(?:(?:noncomputable\s+)?(section|namespace)\b|(end)\b|variable\b(.*(?:\n[ \t]+.*)*))", b[:upto], re.M):
        if m.group(1): stack.append(cur); cur = list(cur)
        elif m.group(2):
            if stack: cur = stack.pop()
        else:
            for g in re.finditer(r"[({]\s*([^:(){}\[\]]+?)\s*:", m.group(3)):
                cur += g.group(1).split()
    out = []
    word = lambda v, x: re.search(r"(?<![\w'.])" + re.escape(v) + r"(?![\w'])", x)
    for v in cur:
        if v not in out and word(v, text) and not word(v, binders): out.append(v)
    return out

class T: pass

def theorems(raw):
    """Every theorem or lemma of a file with its parts, or with .bad naming why it cannot be parsed."""
    b = blank(raw); out = []
    mutual = [(m.start(), b.find("\nend", m.start())) for m in re.finditer(r"^[ \t]*mutual\b", b, re.M)]
    ms = list(THM.finditer(b))
    for m in ms:
        t = T(); t.name = m.group(4); t.start = m.start(); t.indent = len(m.group(1)); t.bad = None
        t.inline = raw[m.start(2):m.end(2)]
        colon, assign = split_sig(b, m.end())
        nx = CMD.search(b, m.end())
        while nx and (len(nx.group()) - len(nx.group().lstrip()) > t.indent) : nx = CMD.search(b, nx.end())
        e = nx.start() if nx else len(b)
        if assign and nx and assign > e:  # a statement line can look like a command only at the wrong column
            t.bad = "command before the proof"
        t.end = len(b[:e].rstrip())
        t.body = b[m.start():t.end]
        if "«" in t.name or not re.fullmatch(r"[^\s:({\[]+", t.name): t.bad = "odd name"
        elif colon is None: t.bad = "no type colon"
        elif assign is None or assign > t.end: t.bad = "no := at depth 0, pattern matching or where style"
        elif any(a < m.start() < z for a, z in mutual): t.bad = "inside mutual"
        else:
            concl = b[colon + 1:assign]
            if re.search(r"(?<![\w'.])(?:let|have|show)(?![\w'])", concl): t.bad = "let or have in the conclusion"
            t.binders = raw[m.end():colon].strip(); t.concl = raw[colon + 1:assign].strip(); t.bconcl = concl.strip()
            t.proof = raw[assign:t.end]
            lines, pre = b[:m.start()].rstrip().split("\n"), []
            for ln in reversed(lines):
                s = ln.strip()
                if not s or s.startswith("@["): continue
                if re.match(r"(?:open|omit|set_option|include|variable)\b.*\bin$", s): pre.insert(0, s); continue
                break
            t.prefix = pre
        out.append(t)
    return out, b

def mutate(raw, b, targets):
    """Scratch text with twins inserted after each target, cut after the last one. Returns text, {twin: (first line, last line)}."""
    pieces, last, twins = [], 0, {}
    line = 1
    def emit(s):
        nonlocal line
        pieces.append(s); line += s.count("\n")
    for t in sorted(targets, key=lambda x: x.end):
        emit(raw[last:t.end]); last = t.end
        ind = " " * t.indent
        forms = []
        if t.binders or t.vars: forms.append(("F", "False"))
        sk = skeleton(t.bconcl)
        if sk and t.concl == t.bconcl: forms.append(("S", sk))
        t.forms = [f for f, _ in forms]
        for f, c in forms:
            twin = f"{t.name}__vac{f}"
            emit("\n\n")
            a = line
            head = t.prefix + [t.inline.strip()] if t.inline.strip() else list(t.prefix)
            if t.vars: head.append("include " + " ".join(t.vars) + " in")
            for h in head: emit(ind + h + "\n")
            emit(f"{ind}theorem {twin} {t.binders} : {c} {t.proof}\n")
            z = line
            twins[twin] = (a, z)
            emit(f"{ind}#print axioms {twin}\n")
    pieces.append("\n")
    return "".join(pieces), twins

ERR = re.compile(r":(\d+):\d+: error\b")
AX = re.compile(r"'([^']*__vac[FS])' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.S)

def compile_file(text, leandir, timeout):
    d = tempfile.mkdtemp(prefix="vacuity-"); p = os.path.join(d, "Mutant.lean")
    with open(p, "w", encoding="utf-8", newline="\n") as f: f.write(text)
    try:
        r = subprocess.run(["lake", "env", "lean", p], cwd=leandir, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired: return None, "timeout"
    except OSError as e: return None, str(e)
    return r.returncode, r.stdout.decode("utf-8", "replace") + r.stderr.decode("utf-8", "replace")

def check_file(f, raw, names, leandir, timeout):
    """names: {theorem: tag} or None for every closed theorem. Returns verdict lines."""
    ts, b = theorems(raw)
    res, targets = [], []
    for t in ts:
        short = t.name.split(".")[-1]
        if names is not None and t.name not in names and short not in names: continue
        tag = (names or {}).get(t.name) or (names or {}).get(short) or "THM"
        t.tag = tag
        if re.search(r"(?<![\w'.])(?:sorry|admit)(?![\w'])", t.body):
            if names is None: continue
        if t.bad: res.append(("UNPARSED", t.name, f"{tag}, {t.bad}")); continue
        if t.bconcl == "False": res.append(("SKIP", t.name, f"{tag}, conclusion already False")); continue
        t.vars = variables_mentioned(b, t.start, t.bconcl + " " + t.proof, t.binders)
        targets.append(t)
    if not targets: return res
    text, twins = mutate(raw, b, targets)
    for t in targets:
        if not t.forms: res.append(("SKIP", t.name, f"{t.tag}, no hypotheses and no skeleton to mutate"));
    targets = [t for t in targets if t.forms]
    if not targets: return res
    rc, out = compile_file(text, leandir, timeout)
    if rc is None:
        return res + [("ERROR", t.name, f"{t.tag}, compile {out[:80]}") for t in targets]
    errs = [int(x) for x in ERR.findall(out)]
    bad = {tw for tw, (a, z) in twins.items() if any(a <= e <= z for e in errs)}
    stray = [e for e in errs if not any(a <= e <= z for a, z in twins.values())]
    ax = {m.group(1).split(".")[-1]: m.group(2) or "" for m in AX.finditer(out)}
    for t in targets:
        hit, sor, lost = None, None, 0
        for f_ in t.forms:
            tw = f"{t.name}__vac{f_}"
            if tw in bad: continue
            a = ax.get(tw.split(".")[-1])
            if a is None: lost += 1; continue  # no error and no axiom report: the twin was never reached, so no verdict
            if "sorryAx" in a: sor = sor or f_
            else: hit = hit or f_
        if hit == "F": res.append(("VACUOUS", t.name, f"{t.tag}, same proof compiles with conclusion False"))
        elif hit == "S": res.append(("VACUOUS_ANTECEDENT", t.name, f"{t.tag}, same proof compiles with the last leaf False"))
        elif sor: res.append(("VIA_SORRY", t.name, f"{t.tag}, form {sor} compiles but only through a sorry"))
        elif lost: res.append(("ERROR", t.name, f"{t.tag}, twin never reached, see the file line"))
        else: res.append(("NOT_FLAGGED", t.name, f"{t.tag}, tried {','.join(t.forms)}"))
    if stray: res.append(("ERROR", "<file>", f"{len(stray)} errors outside the twins, first at scratch line {stray[0]}: {next((l for l in out.splitlines() if ': error' in l), '')[-120:]}"))
    return res

def closed_in(old, new, closed_only):
    o = {t.name: t for t in theorems(old)[0]} if old else {}
    out = {}
    for t in theorems(new)[0]:
        if re.search(r"(?<![\w'.])(?:sorry|admit)(?![\w'])", t.body): continue
        if t.name in o:
            if re.search(r"(?<![\w'.])sorry(?![\w'])", o[t.name].body): out[t.name] = "CLOSED"
        elif not closed_only: out[t.name] = "NEW"
    return out

def main():
    A = sys.argv[1:]
    def opt(k, d=None):
        if k in A:
            i = A.index(k); v = A[i + 1]; del A[i:i + 2]; return v
        return d
    timeout = int(opt("--timeout", "1800")); leandir = opt("--lean-dir", "LeanLab")
    closed_only = "--closed-only" in A
    if closed_only: A.remove("--closed-only")
    file_ = opt("--file"); want = []
    while "--thm" in A: want.append(opt("--thm"))
    R = []
    if file_:
        raw = open(file_, encoding="utf-8", newline="").read().replace("\r\n", "\n")
        names = {w: "NAMED" for w in want} if want else None
        R += [(v, file_, n, d) for v, n, d in check_file(file_, raw, names, leandir, timeout)]
    else:
        base = A[0] if A else sh("git merge-base HEAD origin/main")[1].strip()
        _, files = sh(f"git diff --name-only {base} HEAD -- *.lean")
        for f in [x for x in files.split() if x]:
            if not os.path.exists(f): continue
            raw = open(f, encoding="utf-8", newline="").read().replace("\r\n", "\n")
            rc, old = sh(f"git show {base}:{f}")
            names = closed_in(old if rc == 0 else "", raw, closed_only)
            if names: R += [(v, f, n, d) for v, n, d in check_file(f, raw, names, leandir, timeout)]
    for v, f, n, d in R: print(f"VERDICT {v} {f} {n} {d}", flush=True)
    flagged = sum(v in ("VACUOUS", "VACUOUS_ANTECEDENT", "VIA_SORRY") for v, *_ in R)
    print(f"VACUITY {flagged} flagged of {sum(n != '<file>' for _, _, n, _ in R)}, {sum(v == 'UNPARSED' for v, *_ in R)} unparsed, {sum(v == 'ERROR' for v, *_ in R)} errors")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Lean Lab SEAL CHECK, the Statement Seal gate. Written 2026-10-25 by lean-refresh with Steve live, after a /vet.
Usage, from the repo root, on the branch to judge:  python3 scripts/seal_check.py [BASE]
BASE defaults to git merge-base HEAD origin/main.

What it checks, in every .lean file the branch changed:
  1. SEALED: every theorem, lemma, def, abbrev, structure, class, instance or axiom that exists at BASE keeps the
     exact same statement text, the part before ':=' or 'where', whitespace normalised. A changed or removed
     statement is a FAIL: provers may fill proofs, never edit statements.
  2. NEW TRUST SURFACE: a new axiom, opaque, def or abbrev of type Prop, structure, class or instance is a
     REVIEW item: it can make later theorems vacuous, so a Claude reviewer must read it against the paper.
     New theorems and lemmas are fine: the kernel checks them, and check_branch.sh checks their axioms.
  3. BODIES, lrefresh 2026-10-28 after lean PC NOTE 0803Z: rule 1 cuts at ':=', so an edit inside a def, abbrev,
     instance, structure, class or inductive body was invisible, the Thm5J Thm6J Thm7J Prop edit gave SEAL PASS.
     For every such declaration that exists at BASE, the whole body is compared too; a changed body with the same
     statement is a REVIEW item, never a mechanical merge. Theorem and lemma proofs stay free to change.
     PROP BODIES ARE STATEMENTS, lean architect 2026-10-28 with Steve live: for a def or abbrev whose type ends in
     Prop, the body is the statement itself, so a changed body is a FAIL, exactly as rule 1. Only an ARCHITECT
     statement unit with a DECISION line may pass it, through the reviewer path of the gate table.
  4. A WARN line when the work tree has uncommitted .lean changes: only committed work is checked.
  5. BANNED TOKENS, lproof 2026-11-01 from the public SAIR judge list judge/verify.py and the lab audit, ADDED LINES ONLY:
     code the branch added, comments and strings removed, may not hold an axiom, admit, native_decide, sorryAx, unsafe,
     implemented_by, extern, csimp, metaprogram commands, environment edits or kernel-skip options: see BAN below. FAIL.
     Before this rule check_branch.sh only WARNed on a foreign axiom, so admit passed CI as a closed proof.
  6. MEANING SHIFTS, lproof 2026-11-01: notation, local instance, variable and the like added above a sealed statement
     in the same scope change what that statement means while its text stays equal. REVIEW, see SHIFT below.
     New local notation in a new file is REVIEW too, since macro-class text hides meaning from the reader.
  7. TRUST FILES, lproof 2026-11-01: a branch that changes scripts/, .github/, a lakefile, lean-toolchain or
     lake-manifest.json changes the checker itself, and CI runs the branch's copy. REVIEW.
Prints one line per finding and a last line:
  SEAL PASS            no sealed statement changed and no new trust surface: mechanical merge allowed
  SEAL REVIEW n        no sealed statement changed, n new trust-surface items: Claude review before merge
  SEAL FAIL n          n sealed statements changed or removed: reject, or a Claude reviewer must justify each
"""
import re, subprocess, sys

def sh(c):
    p = subprocess.run(c, shell=True, capture_output=True, text=True)
    return p.returncode, p.stdout

KW = r"(?:theorem|lemma|def|abbrev|structure|class|instance|axiom|opaque|inductive)"
# lproof 2026-11-01: was column 0 with at most one attribute and no local or scoped, so an indented axiom, a local instance
# and open X in theorem were all invisible to the seal.
DECL = re.compile(r"^[ \t]*(?:(?:open|omit|set_option|include)\b[^\n]*?\bin[ \t]+)?(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|local|scoped|public)\s+)*(" + KW + r")\b\s*([^\s:({\[]*)", re.M)

def strip_comments(t, blank_strings=False):
    """Remove Lean comments. Block comments nest in Lean, so a non-greedy regex is wrong: a
    commented-out body holding docstrings left declarations visible. Architect 2026-10-28.
    String aware, lproof 2026-11-01: a string holding /- used to hide the rest of the file from every check.
    blank_strings=True also empties every string literal, for the token scan."""
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and t.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if t[i] == "\n": out.append("\n"); i += 1; continue
            m = _INNER.search(t, i + 1); i = m.start() if m else n; continue
        if t.startswith("--", i):
            j = t.find("\n", i); i = n if j == -1 else j; continue
        if t.startswith("'\"'", i):
            out.append("' '" if blank_strings else "'\"'"); i += 3; continue
        m = _RAW.match(t, i) if t[i] == "r" and (i == 0 or not (t[i - 1].isalnum() or t[i - 1] in "_'.")) else None
        if m or t[i] == '"':
            if m:
                close = '"' + m.group(1); j = t.find(close, m.end()); j = n if j == -1 else j + len(close)
            else:
                j = i + 1
                while j < n and t[j] != '"': j += 2 if t[j] == "\\" else 1
                j = min(j + 1, n)
            s = t[i:j]
            out.append('""' + "\n" * s.count("\n") if blank_strings else s); i = j; continue
        m = _OUTER.search(t, i + 1); j = m.start() if m else n; out.append(t[i:j]); i = j
    return "".join(out)
_RAW = re.compile(r'r(#*)"')
# lmerge 2026-11-02: jump to the next character that matters. The char loop took 1.4 s on a 2 MB certificate, about 20 minutes on
# codex/task227, 337 Lean files, and each timeout wedged the gate queue. Output is byte-identical, tested on those 337 files.
_OUTER = re.compile(r"""/-|--|'"'|"|r#*\"""")
_INNER = re.compile(r"/-|-/|\n")

TOPLVL = re.compile(r"^(?:end|namespace|section|open|variable|universe|attribute|set_option|noncomputable\s+section|#)\b", re.M)

def bodies(text):
    """Map key to normalised full text of non-theorem declarations, trimmed at the next top-level command."""
    text = strip_comments(text)
    out = {}
    full = decls(text, keep_full=True)
    return full

def assign_at(b):
    """Offset of the := that ends a statement: bracket depth 0, skipping let and have inside the statement.
    lproof 2026-11-01: the first := used to win, so a named argument (x := 1) sealed only the text before it."""
    d = 0; lets = 0
    for m in re.finditer(r"[(\[{⦃⟨]|[)\]}⦄⟩]|:=|(?<![\w.'])(?:let|have)(?![\w'])", b):
        x = m.group()
        if x in ("let", "have"): lets += d == 0
        elif x == ":=":
            if d == 0 and lets: lets -= 1
            elif d == 0: return m.start()
        elif x in "([{⦃⟨": d += 1
        else: d -= 1
    return len(b)

def decls(text, keep_full=False):
    """Map (namespace-qualified name, kind) to normalised statement text."""
    text = strip_comments(text)
    out = {}
    ms = list(DECL.finditer(text))
    for i, m in enumerate(ms):
        kind, name = m.group(1), m.group(2) or f"<anon@{m.start()}>"
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        body = text[m.start():end]
        cut = len(body)
        for tok in (" where", "\n  |"):
            j = body.find(tok)
            if j != -1: cut = min(cut, j)
        cut = min(cut, assign_at(body))
        ns = re.findall(r"^\s*namespace\s+(\S+)", text[:m.start()], re.M)
        ends = re.findall(r"^\s*end\s+(\S+)\s*$", text[:m.start()], re.M)
        stack = []
        for line in text[:m.start()].splitlines():
            a = re.match(r"\s*namespace\s+(\S+)", line)
            if a: stack.append(a.group(1)); continue
            b = re.match(r"\s*end\s+(\S+)\s*$", line)
            if b and stack and stack[-1] == b.group(1): stack.pop()
        key = (".".join(stack + [name]), kind)
        if keep_full:
            if kind in ("theorem", "lemma"): continue
            mt = TOPLVL.search(body, 1)
            out[key] = " ".join((body[:mt.start()] if mt else body).split())
        else:
            out[key] = " ".join(body[:cut].split())
    return out

def W(*ws):
    """Whole Lean word, so admit never hits admits or Foo.admit_x; a dotted Lean.ofReduceBool still hits by its last part."""
    return r"(?<![\w'])(?:" + "|".join(ws) + r")(?![\w'])"
# BAN: added code may never hold these. Sources: SAIR judge/verify.py BANNED_PROOF_TOKENS, plus the lab rule, no axiom, admit or
# native_decide, plus kernel and environment hacks the judge does not need to name because it has no such surface.
# Not banned on purpose: @[simp], unif_hint, simproc, local instance of a proved fact: all pass through the kernel.
BAN = {
    "hole": W("sorryAx", "mkSorry") + r"|(?<![\w'.])admit(?![\w'])|(?<![\w'.])stop(?=\s*$)",
    "axiom": r"(?<![\w'.«])axiom(?![\w'»])",
    "native": W("native_decide", "ofReduceBool", "ofReduceNat", "reduceBool", "reduceNat", "trustCompiler") + r"|\bdecide\s*\+native|native\s*:=\s*true",
    "kernel_skip": r"\b(?:debug|bootstrap)\.\w+|" + W("skipKernelTC", "addDeclWithoutChecking"),
    "unsafe": W("unsafe", "unsafeCast", "unsafeIO", "unsafeBaseIO", "unsafeEIO", "unsafePerformIO", "implemented_by", "extern", "csimp", "ptrAddrUnsafe", "lcProof", "lcUnreachable"),
    "metaprogram": r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|local|scoped)\s+)*(?:elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|initialize|builtin_initialize|meta)\b"
                   + r"|" + W("run_cmd", "run_elab", "run_meta", "run_tac") + r"|#(?:eval|exit|reduce|check_eval|synth)\b",
    "metaattr": r"@\[[^\]]*\b(?:init|builtin_init|tactic|command_elab|term_elab|macro|builtin_\w+|app_unexpander|delab|command_parser|term_parser)\b",
    "environment": W("addDecl", "addAndCompile", "modifyEnv", "setEnv", "importModules", "withImportModules", "evalDecl", "evalConst", "evalConstCheck", "evalTerm", "evalExpr"),
}
# SHIFT: harmless in a new lemma's own file, but above a sealed statement in the same scope it changes that statement.
# A plain open is left out on purpose: 22 of 700 real merges added one above a sealed statement, all harmless, and a REVIEW auto-rejects digger lanes.
NOTATION = r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|local|scoped)\s+)*(?:notation\d?|notation3|infix[lr]?|prefix|postfix)\b"
SHIFT = {
    "notation": NOTATION,
    "instance": r"^\s*(?:@\[[^\]]*\]\s*)*(?:local|scoped)\s+instance\b|^\s*attribute\s*\[[^\]]*\binstance\b(?![^\]]*\]\s*Classical\.)|^\s*deriving\s+instance\b",
    "variable": r"^\s*(?:variable|include|universe|export)\b",
}
TRUST = re.compile(r"^(?:\.github/|scripts/|(?:LeanLab/)?(?:lakefile\.\w+|lean-toolchain|lake-manifest\.json)$)")

def added_lines(old, new):
    """(index in new, text) of code lines the branch added: comments and strings removed, a line counts as added
    once its stripped text occurs more often than at BASE. Line based, so a move inside a file adds nothing."""
    from collections import Counter
    have = Counter(l.strip() for l in old.splitlines() if l.strip())
    out = []
    for i, l in enumerate(new.splitlines()):
        k = l.strip()
        if not k: continue
        if have[k] > 0: have[k] -= 1
        else: out.append((i, l))
    return out

def scope_hits_sealed(lines, i, sealed):
    """A sealed declaration below line i and before the section or namespace holding line i closes."""
    d = 0
    for l in lines[i + 1:]:
        if re.match(r"\s*(?:noncomputable\s+)?(?:section|namespace)\b", l): d += 1
        elif re.match(r"\s*end\b", l):
            d -= 1
            if d < 0: return None
        m = DECL.match(l)
        if m and m.group(2) and m.group(2).split(".")[-1] in sealed: return m.group(2)
    return None

def token_scan(f, old, new, sealed):
    """Rules 5 and 6 on one file. old is empty for a new file. Returns (fails, reviews) as printable lines."""
    fails, reviews = [], []
    o = strip_comments(old, True); n = strip_comments(new, True); nl = n.splitlines()
    for i, l in added_lines(o, n):
        for why, rx in BAN.items():
            if re.search(rx, l):
                fails.append(f"FAIL banned {why} in {f}: {l.strip()[:160]}"); break
        for why, rx in SHIFT.items():
            if not re.search(rx, l): continue
            hit = scope_hits_sealed(nl, i, sealed) if old else None
            if hit: reviews.append(f"REVIEW {why} added above sealed {hit} in {f}: {l.strip()[:160]}")
            elif why == "notation" and not old: reviews.append(f"REVIEW new notation in new file {f}: {l.strip()[:160]}")
            elif why == "instance": reviews.append(f"REVIEW new {why} in {f}: {l.strip()[:160]}")
            break
    return fails, reviews

def main():
    base = sys.argv[1] if len(sys.argv) > 1 else sh("git merge-base HEAD origin/main")[1].strip()
    if not base:
        print("SEAL FAIL 1  no merge base; git fetch origin main first"); return 2
    _, files = sh(f"git diff --name-only {base} HEAD -- '*.lean'")
    fails = reviews = 0
    A, B, where = {}, {}, {}
    FA, FB = {}, {}
    _, every = sh(f"git diff --name-only {base} HEAD")
    for t in [x for x in every.split() if TRUST.match(x)]:
        print(f"REVIEW trust file changed: {t}"); reviews += 1
    rc_st, dirty = sh("git status --porcelain -- '*.lean'")
    if dirty.strip(): print("WARN uncommitted .lean changes are not checked; commit them first")
    for f in [x for x in files.split() if x]:
        rc_old, old = sh(f"git show {base}:'{f}'")
        rc_new, new = sh(f"git show HEAD:'{f}'")
        if rc_old == 0: A.update(decls(old)); FA.update(bodies(old))
        if rc_new == 0:
            d = decls(new); B.update(d); where.update({k: f for k in d}); FB.update(bodies(new))
            sealed = {k[0].split(".")[-1] for k in decls(old)} if rc_old == 0 else set()
            fl, rv = token_scan(f, old if rc_old == 0 else "", new, sealed)
            for l in fl + rv: print(l)
            fails += len(fl); reviews += len(rv)
    # a declaration moved between changed files keeps its name: compare across all changed files together
    for k, s in A.items():
        if k not in B:
            print(f"FAIL removed {k[1]} {k[0]}"); fails += 1
        elif B[k] != s:
            print(f"FAIL changed {k[1]} {k[0]} in {where[k]}\n  was: {s[:300]}\n  now: {B[k][:300]}"); fails += 1
    for k, s in FA.items():
        if k in FB and k in B and B[k] == A.get(k) and FB[k] != s:
            if k[1] in ("def", "abbrev") and re.search(r":\s*(?:[^:=]*→\s*)?Prop\s*$", A[k]):
                # the body of a Prop-valued def IS the statement, so a change is a sealed-statement change
                print(f"FAIL changed Prop body {k[1]} {k[0]} in {where[k]}\n  was: {s[:300]}\n  now: {FB[k][:300]}"); fails += 1
            else:
                print(f"REVIEW changed body {k[1]} {k[0]} in {where[k]}\n  was: {s[:300]}\n  now: {FB[k][:300]}"); reviews += 1
    for k, s in B.items():
        if k in A: continue
        kind = k[1]
        prop_def = kind in ("def", "abbrev") and re.search(r":\s*Prop\b|→\s*Prop\s*$", s)
        if kind in ("axiom", "opaque", "structure", "class", "instance", "inductive") or prop_def:
            print(f"REVIEW new {kind} {k[0]} in {where[k]}: {s[:300]}"); reviews += 1
    if fails: print(f"SEAL FAIL {fails}"); return 1
    if reviews: print(f"SEAL REVIEW {reviews}"); return 0
    print("SEAL PASS"); return 0

if __name__ == "__main__":
    sys.exit(main())

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
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(" + KW + r")\b\s*([^\s:({\[]*)", re.M)

def strip_comments(t):
    """Remove Lean comments. Block comments nest in Lean, so a non-greedy regex is wrong: a
    commented-out body holding docstrings left declarations visible. Architect 2026-10-28."""
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and t.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if t[i] == "\n": out.append("\n")
            i += 1; continue
        if t.startswith("--", i):
            j = t.find("\n", i); i = n if j == -1 else j; continue
        out.append(t[i]); i += 1
    return "".join(out)

TOPLVL = re.compile(r"^(?:end|namespace|section|open|variable|universe|attribute|set_option|noncomputable\s+section|#)\b", re.M)

def bodies(text):
    """Map key to normalised full text of non-theorem declarations, trimmed at the next top-level command."""
    text = strip_comments(text)
    out = {}
    full = decls(text, keep_full=True)
    return full

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
        for tok in (":=", " where", "\n  |"):
            j = body.find(tok)
            if j != -1: cut = min(cut, j)
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

def main():
    base = sys.argv[1] if len(sys.argv) > 1 else sh("git merge-base HEAD origin/main")[1].strip()
    if not base:
        print("SEAL FAIL 1  no merge base; git fetch origin main first"); return 2
    _, files = sh(f"git diff --name-only {base} HEAD -- '*.lean'")
    fails = reviews = 0
    A, B, where = {}, {}, {}
    FA, FB = {}, {}
    rc_st, dirty = sh("git status --porcelain -- '*.lean'")
    if dirty.strip(): print("WARN uncommitted .lean changes are not checked; commit them first")
    for f in [x for x in files.split() if x]:
        rc_old, old = sh(f"git show {base}:'{f}'")
        rc_new, new = sh(f"git show HEAD:'{f}'")
        if rc_old == 0: A.update(decls(old)); FA.update(bodies(old))
        if rc_new == 0:
            d = decls(new); B.update(d); where.update({k: f for k in d}); FB.update(bodies(new))
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
        prop_def = kind in ("def", "abbrev") and re.search(r":\s*Prop\b", s)
        if kind in ("axiom", "opaque", "structure", "class", "instance", "inductive") or prop_def:
            print(f"REVIEW new {kind} {k[0]} in {where[k]}: {s[:300]}"); reviews += 1
    if fails: print(f"SEAL FAIL {fails}"); return 1
    if reviews: print(f"SEAL REVIEW {reviews}"); return 0
    print("SEAL PASS"); return 0

if __name__ == "__main__":
    sys.exit(main())

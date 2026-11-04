#!/usr/bin/env python3
"""FINISH ranking: distance of each paper folder to a Palomar entry. Static, no Lean run.

Usage:
  python3 scripts/finish_rank.py CHECKOUT [--md TABLE.md] [--json OUT.json] [--finish LINES.txt]
                                 [--main Folder=Decl.Name ...] [--explain Decl.Name ...] [--candidates]

CHECKOUT is a repo checkout, the folder that holds LeanLab/LeanLab/<Folder>/; a plain copy without .git works.
With no --md it prints the table to stdout. --main replaces or adds a main theorem for one run; keep lasting changes
in CURATED below. --explain prints the sorry closure of a declaration with one reference path to each sorry.
--candidates prints, per row, the folder's other theorems with the same conclusion, which finds finer or shorter routes.
--finish writes the top 10 as `- FINISH <Folder> <theorem> <sorries left>` lines, header not included.
Cost: about 1 to 2 minutes and 1 GB over 5000 files with Python 3.10 or later, stdlib only.

Method. Parses every LeanLab/LeanLab/**/*.lean, excluding /old/. Comments and strings are blanked. Declarations:
theorem lemma def abbrev structure class inductive instance opaque axiom alias. Scopes: namespace, section, mutual, end,
open, open .. in, variable. Identifiers resolve as Lean resolves them: enclosing namespaces longest first, then open
namespaces and root, restricted to the file's transitive imports. From each main theorem it walks the reference graph
and counts declarations whose body contains sorry, one per declaration, as OPEN or CITED by the rule of
scripts/mountain.py, whose regexes are copied here and must stay in step with it.
Followed beyond the old 2026-11-01 script: anonymous and named instances through their class head, dot notation
x.foo when Type.foo exists and Type is referenced by the same declaration, Type.field to Type, and section variables
whose names the declaration uses. Local binders that shadow a lab name are dropped.
Not followed: notation and macro bodies. Known bias: both directions are possible; a Lean walk of the environment
is the ground truth for one declaration.

Row flags. STUB: the main is itself sorry or a Prop with no proof, so its count 1 hides the whole paper; never a FINISH
line. CONDITIONAL: statement hypotheses of the main, which add no sorry. NATIVE: closure uses native_decide, so
#print axioms shows Lean.ofReduceBool. AXIOM: closure holds a lab axiom. auto: no curated main, the theorem with the
largest in-folder closure stands in and is not a FINISH line either, as in the 2026-11-01 ranking.
HOLLOW and REFUTED: see the tables of those names below; neither gets a FINISH line.
"""
import argparse, collections, json, os, re, sys

# --- the mountain.py convention, copied verbatim
CITED_RE = re.compile(r"\bcited\b|not proved in the lab|\bquoted\b|taken from the paper|\bpublished\b|paper\W+cited", re.I)
LINE_COMMENT = re.compile(r"(?<![/-])--(?!-)[^\n]*")

# Folders that are helpers or ports, reported but never ranked.
EXCLUDED = {"ChenPrimeExceptional", "Common", "HelfgottOverview", "KaiScaffolding", "PNTPort", "PNTSieve", "Ported",
            "Routes", "Schnirelmann", "SchnirelmannConstant", "Verifications", "OAIQuasiRiemann"}

# (Folder, main theorem, method). Several lines for one folder: the smallest closure wins, non-STUB preferred.
# Started from research/finish-ranking-20261101T0802Z.md; add a line when a clearly better main appears.
CURATED = [
    ("BHP1997", "LeanLab.BHP1997.AssemblyC165.theorem1", "curated"),  # Decomp132.theorem1 rests on a dead duplicate sieve_data, architect 20261103
    ("BS2022GRH", "thm5J_assembly", "curated"),
    ("BS2022GRH", "LeanLab.BS2022GRH.DecompC169a.thm5J", "curated"),
    ("Helfgott2013", "LeanLab.Helfgott2013.U1538.prop62_arcs", "auto"),
    ("Linnik", "LeanLab.Linnik.Decomp1532c.theorem1_of_leaves", "curated"),
    ("BakerHarmanPintz1997", "LeanLab.BakerHarmanPintz1997.theorem1_of_theorem2_15", "curated"),  # U-1613: theorem1_via_prop12 is hollow, prop12 is display 1.2
    ("HelfgottMajor", "LeanLab.HelfgottMajor.Decomp123.theorem_1_1", "curated"),
    ("LanguascoPintzZaccagnini2007", "LeanLab.LPZ2007.repaired_mainJ131", "curated"),
    ("Linnik1951", "LeanLab.Linnik1951.linnik1951_decomposed111", "curated"),
    ("AlmostPrimeSums", "LeanLab.AlmostPrimeSums.Chen1973Own.ChenTheoremI", "curated"),
    ("AlmostPrimes", "LeanLab.AlmostPrimes.johnston_starichkova", "curated"),
    ("ChenDoubleSieve", "LeanLab.ChenDoubleSieve.wu2004_thm1", "curated"),
    ("ChirreHagen2025", "LeanLab.ChirreHagen2025.theorem1", "curated"),
    ("Grimmelt2019", "LeanLab.Grimmelt2019.grimmelt_thm1_1", "curated"),
    ("Halupczok2012", "LeanLab.Halupczok2012.theorem_2", "curated"),
    ("Hathi2021", "LeanLab.Hathi2021.theorem_1_1", "curated"),
    ("LZPowersOfTwo", "LeanLab.LZPowersOfTwo.lz_theorem_tr", "curated"),
    ("LanguascoPerelli1996", "LeanLab.LanguascoPerelli1996.theorem1", "curated"),
    ("Li2024", "LeanLab.Li2024.theorem1_1_v3_stmt", "curated"),
    ("LiuTsang2005", "LeanLab.LiuTsang2005.Theorem11i", "curated"),
    ("MissingDigit", "LeanLab.MissingDigit.kim_thm1_1", "curated"),
    ("PerelliPintz1992", "LeanLab.PerelliPintz1992.perelliPintz", "curated"),
    ("RamareSaouter2003", "LeanLab.RamareSaouter2003.theorem1_stmt", "curated"),
    ("Ternary", "LeanLab.Ternary.mms_theorem11", "curated"),
    ("Xi2012", "LeanLab.Xi2012.NatEncoding.Theorem1Even", "curated"),
    ("Akeno2026", "LeanLab.Akeno2026.DecompJ267.akeno_thm1_1_assembled", "curated"),
    ("Stein1965", "LeanLab.Stein1965.Decomp114.sparsePrimeBasis_assembled", "curated"),
    ("Zhao2025", "LeanLab.Zhao2025.Task292.PaperTheorem14_assembly", "curated"),
    ("Zhan1991", "LeanLab.Zhan1991.theorem1_decomp110", "curated"),
    ("DtRS1998", "LeanLab.DtRS1998.Decomp121b.theorem2", "curated"),
    ("HelfgottArcs", "LeanLab.HelfgottArcs.major_1_1'", "curated"),
    ("KumchevLiu2007", "LeanLab.KumchevLiu2007.Task129.thm1_from_leaves", "curated"),
    ("Ramare1995", "LeanLab.Ramare1995.theorem1", "curated"),
    ("Tolev2009", "LeanLab.Tolev2009.Decomp83.legacy_assembly", "curated"),
    ("SchnirelmannBounds", "LeanLab.SchnirelmannBounds.Decomp1525b.lemma8_of", "auto"),
    ("LPZ2007", "LeanLab.LPZ2007.lpz_main_J_twoC0_minor", "curated"),
    ("LiuWang2002", "LeanLab.LiuWang2002.U1543.task147_m4_inclusive", "auto"),
    ("Cai2002", "LeanLab.Cai2002.main_theorem_decomp118", "curated"),
    ("ExceptionalSet", "LeanLab.ExceptionalSet.DecompJ200.brudernPerelli_assembly", "curated"),
    ("BhowmikGrimmelt2026", "LeanLab.BhowmikGrimmelt2026.theorem31_decomposed150", "curated"),
    ("Song2020", "LeanLab.Song2020.DecompJ198.song_theorem1_decomposed", "curated"),
    ("Teravainen2016", "LeanLab.Teravainen2016.theorem_1_1", "curated"),
    ("KadiriLumley2014", "LeanLab.KadiriLumley2014.corollary1_2", "curated"),
    ("Perelli1996", "LeanLab.Perelli1996.B.perelli_theorem1", "curated"),
    ("Brun1919", "LeanLab.Brun1919.brun", "curated"),
    ("BrunGap", "LeanLab.BrunGap.many_large_gaps", "auto"),
    ("ChebyshevExplicit", "LeanLab.ChebyshevExplicit.pi_chebyshev30_interval_vacuity", "auto"),
    ("DensityGoldbach", "LeanLab.DensityGoldbach.alsetri_1_2_proved", "curated"),
    ("Estermann1938", "LeanLab.Estermann1938.main", "curated"),
    ("GoldbachAverage", "LeanLab.GoldbachAverage.gs_theorem1", "curated"),
    ("GoldbachGaps", "LeanLab.GoldbachGaps.Goldston1990.theorem6_proved", "curated"),
    ("GvLtR1989", "LeanLab.GvLtR1989.gvltr_ratio_upTo2", "auto"),
    ("HardyLittlewood1923", "LeanLab.HardyLittlewood1923.theoremB", "curated"),
    ("HelfgottPlatt", "LeanLab.HelfgottPlatt.ternaryGoldbachUpTo_1e8", "auto"),
    ("Martin2018", "LeanLab.Martin2018.conj1_7_upTo_big", "auto"),
    ("OeSHP2014", "LeanLab.OeSHP2014.table9_isGap", "auto"),
    ("Pintz2018", "LeanLab.Pintz2018.Instances117.vacuity_residual", "auto"),
    ("PlattTrudgian2014", "LeanLab.PlattTrudgian2014.lambdaPositiveThreshold_uncond_h2", "auto"),
    ("Ricci1937", "LeanLab.Ricci1937.theoremB", "curated"),
    ("Saouter1998", "LeanLab.Saouter1998.Thm1.theorem1", "curated"),
    ("SchnirelmannExplicit", "LeanLab.SchnirelmannExplicit.Sharper6.schnirelmann_bounded_primes_H₆", "auto"),
    ("SchnirelmannGoldbach", "LeanLab.SchnirelmannGoldbach.schnirelmann_bounded_primes", "curated"),
    ("Sinisalo1993", "LeanLab.Sinisalo1993.table2_minGB", "auto"),
    ("SteinStein1965", "LeanLab.SteinStein1965.no_single_choice_before316", "auto"),
    ("Tchudakov1938", "LeanLab.Tchudakov1938.theorem1", "curated"),
    ("VanDerCorput1939", "LeanLab.VanDerCorput1939.vinogradov1", "auto"),
    ("ChenExplicit", "LeanLab.ChenExplicit.Yamada.U1391.yamada_of_sieve_rs75", "curated"),
    ("DERZ1997", "LeanLab.DERZ1997.derz_main_of", "curated"),
    ("Dudek2014", "LeanLab.Dudek2014.Retired2.theorem1_stmt_of", "curated"),
    ("GRHComputations", "LeanLab.GRHComputations.platt_height200", "auto"),
    ("GoldbachShort78", "LeanLab.GoldbachShort78.goldbach_short_of_printed_counts", "curated"),
    ("HeathBrown1985", "LeanLab.HeathBrown1985.theorem1_of_siegelWalfisz", "curated"),
    ("HeathBrownPuchta", "LeanLab.HeathBrownPuchta.SReduction.C2_le_of_mphi", "auto"),
    ("JohnstonStarichkova", "LeanLab.JohnstonStarichkova.theorem1_4", "curated"),
    ("Kaniecki1995", "LeanLab.Kaniecki1995.L5.theoremOdd_of_lemma4G_K4", "curated"),
    ("KanieckiGap", "LeanLab.KanieckiGap.Decomp127b.real_interval_from_guarded", "auto"),
    ("LZCesaroShort", "LeanLab.LZCesaroShort.lz_theorem1_printed", "curated"),
    ("Languasco2004", "LeanLab.Languasco2004.EncA.theorem1_6_of_perelliRemark", "auto"),
    ("Pintz2021", "LeanLab.Pintz2021.Theorem1U1369.exponent_of_221", "auto"),
    ("PrimePowerWindow", "LeanLab.PNTPort.ExplicitPsi1.Trivial.goldbach_gap_1478_RH_trudgian_W", "auto"),
    ("Richstein2001", "LeanLab.Richstein2001.gvltr_sup_of", "auto"),
    ("RieselVaughan1983", "LeanLab.RieselVaughan1983.Section9Lemma6.theorem_LS3", "curated"),
    ("Romanov", "LeanLab.Romanov.gallagher_eta_arc_le", "auto"),
    ("SparseTernary", "LeanLab.SparseTernary.Gluing.theorem11_of_lemma31", "curated"),
    ("Tao2012", "LeanLab.Tao2012.theorem1_4", "curated"),
    ("Ternary78", "LeanLab.Ternary78.Bennett.actual_model_gap", "auto"),
    ("Vaughan1979", "LeanLab.Vaughan1979.chain", "auto"),
    ("Zinoviev1997", "LeanLab.Zinoviev1997.zinoviev_of_local", "auto"),
    ("ChenPrimeExceptional", "LeanLab.ChenPrimeExceptional.Task58.c0_bracket_unconditional", "auto"),
    ("Common", "LeanLab.Common.PsiTheta.schoenfeld_of_rs_from", "auto"),
    ("HelfgottOverview", "LeanLab.HelfgottOverview.history_of_helfgott", "auto"),
    ("KaiScaffolding", "LeanLab.KaiScaffolding.a_3807404", "auto"),
    ("PNTPort", "LeanLab.PNTPort.BVMax.twin6_infinite", "auto"),
    ("PNTSieve", "LeanLab.PNTSieve.BrunTitchmarsh.card_range_filter_isPrimePow_le", "auto"),
    ("Ported", "LeanLab.Ported.Prove2Me.Decomp1525cLink.lemma11_of_eq215", "auto"),
    ("Routes", "LeanLab.Routes.U1556B.goldbach_219_all", "auto"),
    ("Schnirelmann", "LeanLab.Schnirelmann.Mann.ceil_inv_density_nsmul_eq_univ", "auto"),
    ("SchnirelmannConstant", "LeanLab.SchnirelmannConstant.atMost2_of_even", "auto"),
    ("Verifications", "LeanLab.Verifications.Top50.Bits.minGB_max_upTo_1e9", "auto"),
]

# Leaves a kernel check shows cannot be proved as stated. A main whose closure holds one loses to any other route,
# and it never gets a FINISH line. leaf_comb: leaf_comb_excludes_GRH in BS2022GRH/DecompJ215.lean turns it into a
# proof of not GRH, so the leaf could only be proved by refuting GRH.
REFUTED = {"leaf_comb"}

# Rows whose assembly is real Lean but whose leaves restate the theorem. Same treatment as STUB for the FINISH lines.
# Judged by reading the statements, recheck when the folder changes. Reason text goes in the Flags column.
HOLLOW = {
    "Akeno2026": "leaf thm1_1_base_case_k0 has the statement of the main, the other leaf is X implies X",
    "HelfgottArcs": "leaf major_1_1 is the theorem itself, the assembly only discharges the GRH input by Platt",
    "Ramare1995": "the two leaves are the theorem split at 10^30",
}

MODS = r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|public|local|scoped|meta)\s+)*"
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
KINDS = r"theorem|lemma|def|abbrev|structure|class\s+abbrev|class\s+inductive|class|inductive|instance|opaque|axiom|example|alias"
DECL_RE = re.compile(r"^[ \t]*" + ATTRS + MODS + r"(?P<kind>" + KINDS + r")\b", re.M)
SCOPE_RE = re.compile(r"^[ \t]*(?:(?P<ns>namespace)\s+(?P<nsname>[^\s]+)|(?:(?:noncomputable|public)\s+)*(?P<sec>section)\b[ \t]*(?P<secname>[^\s]*)"
                      r"|(?P<mut>mutual)\b|(?P<end>end)\b[ \t]*(?P<endname>[^\s]*))", re.M)
CMD_RE = re.compile(r"^(?P<cmd>open|variable|omit|include|universe|set_option|attribute|notation|local notation|scoped notation|macro|syntax|elab|"
                    r"infixl|infixr|infix|prefix|postfix|initialize|deriving|#[a-z_]+|export|add_decl_doc|run_cmd|library_note|assert_not_exists)\b", re.M)
IMPORT_RE = re.compile(r"^(?:public\s+|meta\s+)*import\s+(?:all\s+)?(\S+)", re.M)
IDENT = r"(?:[^\W\d]|«)[\w'!?«»]*"
TOKEN_RE = re.compile(r"(?<![\w'!?»])\.?" + IDENT + r"(?:\." + IDENT + r")*")
BINDER_RE = re.compile(r"[(\{\[⦃]\s*((?:[^\W\d][\w'!?]*\s+)*[^\W\d][\w'!?]*)\s*:(?!=)")
LOCAL_RE = re.compile(r"\b(?:have|let|set|obtain|show|suffices)\s+([^\W\d][\w'!?]*)\b")
LAMBDA_RE = re.compile(r"(?:\bfun\b|λ|∀|∃|Σ|∑|∏|\bintro\b|\bintros\b|\brintro\b|\brcases\b|\bobtain\b|\bcases\b|\binduction\b)([^,=:\n⟨]*(?:⟨[^⟩\n]*⟩[^,=:\n]*)*)")
NAMED_ARG_RE = re.compile(r"\(\s*([^\W\d][\w'!?]*)\s*:=")
FIELD_RE = re.compile(r"^\s*([^\W\d][\w'!?]*)\s*:=", re.M)
STOP = set("""theorem lemma def abbrev structure class inductive instance by at with from fun let have show suffices obtain
 if then else match do where forall exists Type Sort Prop this rfl simp rw exact apply intro intros refine calc open in
 namespace section end variable universe noncomputable private protected nat_cast""".split())
OPENERS = "([{⟨⦃"; CLOSERS = ")]}⟩⦄"


def blank(raw):
    """Same length as raw, comments and string bodies replaced by spaces, newlines kept."""
    out = list(raw); i = 0; n = len(raw)
    def wipe(a, b):
        for k in range(a, b):
            if out[k] != "\n": out[k] = " "
    while i < n:
        c = raw[i]
        if c == "-" and raw.startswith("--", i):
            j = raw.find("\n", i); j = n if j < 0 else j
            wipe(i, j); i = j
        elif c == "/" and raw.startswith("/-", i):
            d = 1; j = i + 2
            while j < n and d:
                if raw.startswith("/-", j): d += 1; j += 2
                elif raw.startswith("-/", j): d -= 1; j += 2
                else: j += 1
            wipe(i, j); i = j
        elif c == '"':
            if i and raw[i - 1] == "'" and raw[i + 1:i + 2] == "'": i += 2; continue
            j = i + 1
            while j < n and raw[j] != '"':
                j += 2 if raw[j] == "\\" else 1
            wipe(i + 1, min(j, n)); i = j + 1
        else:
            i += 1
    return "".join(out)


class Decl:
    __slots__ = ("name", "kind", "file", "folder", "line", "text", "ns", "opens", "variables", "sorry", "cls", "native",
                 "head_class", "tokens", "named", "prefix_chain", "start")


def split_signature(text):
    """Return (binders, type, rest) of a declaration text, cut at top level."""
    depth = 0; i = 0; n = len(text); colon = -1
    while i < n:
        c = text[i]
        if c in OPENERS: depth += 1
        elif c in CLOSERS: depth -= 1
        elif depth == 0:
            if text.startswith(":=", i):
                return (text[:colon], text[colon + 1:i], text[i:]) if colon >= 0 else (text[:i], "", text[i:])
            if c == ":" and colon < 0: colon = i
            elif colon >= 0 and text.startswith("where", i) and text[i - 1].isspace(): return text[:colon], text[colon + 1:i], text[i:]
            elif colon >= 0 and c == "|" and text[i - 1] == "\n": return text[:colon], text[colon + 1:i], text[i:]
            elif colon < 0 and text.startswith("where", i) and text[i - 1].isspace(): return text[:i], "", text[i:]
        i += 1
    if colon >= 0: return text[:colon], text[colon + 1:], ""
    return text, "", ""


def split_binders(sig):
    """Top level bracket groups of a signature, as (open char, inner text)."""
    out = []; depth = 0; start = 0
    for i, c in enumerate(sig):
        if c in OPENERS:
            if depth == 0: start = i
            depth += 1
        elif c in CLOSERS:
            depth -= 1
            if depth == 0: out.append((sig[start], sig[start + 1:i]))
    return out


class Index:
    def __init__(self, root):
        self.root = root; self.src = os.path.join(root, "LeanLab", "LeanLab")
        if not os.path.isdir(self.src): sys.exit(f"finish_rank: {self.src} not found; give the repo checkout path")
        self.names = collections.defaultdict(list); self.tails = collections.defaultdict(list)
        self.decls = []; self.imports = {}; self.vis = {}; self.edges = {}; self.instances = collections.defaultdict(list)
        self.by_file = collections.defaultdict(list); self.folder_decls = collections.defaultdict(list)
        self.nsknown = set()
        for dp, dn, fn in os.walk(self.src):
            dn[:] = sorted(d for d in dn if d != "old")
            for f in sorted(fn):
                if f.endswith(".lean"): self.parse(os.path.join(dp, f))
        for d in self.decls:
            if d.sorry: self.classify_done = True

    def module(self, path):
        rel = os.path.relpath(path, os.path.join(self.root, "LeanLab"))
        return rel[:-5].replace(os.sep, ".")

    def parse(self, path):
        raw = open(path, encoding="utf8", errors="replace").read(); code = blank(raw); mod = self.module(path)
        folder = mod.split(".")[1] if mod.count(".") >= 2 else mod.split(".")[-1]
        self.imports[mod] = [m for m in IMPORT_RE.findall(code) if m.startswith("LeanLab.")]
        file_cited = path.endswith("/Statements.lean") or bool(re.search(
            r"sorry[^.]{0,40}marks a statement taken from the paper|statements? taken from the paper", raw[:1500], re.I))
        ev = [(m.start(), "decl", m) for m in DECL_RE.finditer(code)]
        ev += [(m.start(), "scope", m) for m in SCOPE_RE.finditer(code)]
        ev += [(m.start(), "cmd", m) for m in CMD_RE.finditer(code)]
        ev.sort(key=lambda e: e[0])
        ends = [e[0] for e in ev] + [len(code)]
        stack = [{"ns": "", "opens": [], "vars": []}]; pending_opens = []
        for i, (pos, typ, m) in enumerate(ev):
            end = ends[i + 1]
            while i + 1 < len(ev) and end == pos: end = len(code); break
            seg = code[pos:end]
            if typ == "scope":
                if m.group("ns"):
                    stack.append({"ns": (stack[-1]["ns"] + "." if stack[-1]["ns"] else "") + m.group("nsname"), "opens": list(stack[-1]["opens"]), "vars": list(stack[-1]["vars"])})
                elif m.group("sec") or m.group("mut"):
                    stack.append({"ns": stack[-1]["ns"], "opens": list(stack[-1]["opens"]), "vars": list(stack[-1]["vars"])})
                elif m.group("end") and len(stack) > 1:
                    stack.pop()
            elif typ == "cmd":
                cmd = m.group("cmd")
                if cmd == "open":
                    body = seg[4:]; has_in = re.search(r"\bin\s*$", body.strip()) is not None
                    body = re.sub(r"\bin\s*$", "", body.strip())
                    body = re.sub(r"\(.*?\)", " ", body, flags=re.S)
                    body = re.split(r"\b(?:hiding|renaming)\b", body)[0]
                    nss = [t for t in body.split() if t not in ("scoped",)]
                    (pending_opens if has_in else stack[-1]["opens"]).extend(nss)
                elif cmd == "variable":
                    stack[-1]["vars"].extend(split_binders(seg[8:]))
            elif typ == "decl":
                self.add_decl(path, mod, folder, raw, code, m, seg, pos, stack[-1], pending_opens, file_cited)
                pending_opens = []

    def add_decl(self, path, mod, folder, raw, code, m, seg, pos, scope, pend, file_cited):
        kind = m.group("kind").split()[-1] if m.group("kind").startswith("class") else m.group("kind")
        rest = code[m.end():pos + len(seg)]
        name = ""; after = rest.lstrip()
        if kind == "instance":
            after2 = re.sub(r"^\(priority\s*:=[^)]*\)\s*", "", after)
            nm = re.match(r"(" + IDENT + r"(?:\." + IDENT + r")*)", after2)
            if nm and not after2.startswith(":"): name = nm.group(1); after = after2[nm.end():]
            else: after = after2
        elif kind == "example":
            name = ""
        else:
            nm = re.match(r"(" + IDENT + r"(?:\." + IDENT + r")*)", after)
            if nm: name = nm.group(1); after = after[nm.end():]
        line = code.count("\n", 0, pos) + 1
        d = Decl(); d.kind = kind; d.file = path; d.folder = folder; d.line = line; d.text = after; d.start = pos
        d.ns = scope["ns"]; d.opens = scope["opens"] + list(pend); d.variables = scope["vars"]
        if name.startswith("_root_."): full = name[7:]
        elif name: full = (scope["ns"] + "." if scope["ns"] else "") + name
        else: full = f"{kind}@{os.path.relpath(path, self.src)}:{line}"
        d.name = full
        d.sorry = bool(re.search(r"(?<![\w.])sorry\b", after)); d.native = "native_decide" in after or kind == "axiom"
        d.cls = self.classify(raw, pos, after, file_cited, kind, name) if d.sorry else ""
        d.head_class = None
        if kind == "instance":
            sig, ty, _ = split_signature(after)
            hd = re.findall(TOKEN_RE, ty)
            d.head_class = hd[0] if hd else None
        d.tokens = None; d.named = bool(name)
        self.decls.append(d); self.by_file[mod].append(d); self.folder_decls[folder].append(d)
        if kind != "example":
            self.names[full].append((mod, d))
            parts = full.split(".")
            for k in range(1, len(parts)):
                self.tails[".".join(parts[k:])].append((mod, d)); self.nsknown.add(".".join(parts[:k]))
        if kind == "instance" and d.head_class:
            self.instances[d.head_class.split(".")[-1]].append((mod, d))

    def classify(self, raw, pos, after, file_cited, kind, name):
        prefix = LINE_COMMENT.sub("", raw[:pos])
        doc = prefix[-600:]
        d = doc.rfind("/--"); docs = doc[d:] if d != -1 and "-/" in doc[d:] else ""
        s = prefix.rfind("/-!"); section = prefix[s:s + 300] if s != -1 else ""
        unit = re.search(r"\bUnit U-\d+", docs)
        body = f"{kind} {name}{after}".strip()
        paper_main = re.search(r"\bP\d{4}\b", docs) or re.match(r"(?:theorem|lemma)\s+\S+\s*:\s*[A-Z][\w.]*\s*:=\s*by\s+sorry", body)
        if CITED_RE.search(docs) or (not unit and (CITED_RE.search(section) or file_cited or paper_main)): return "CITED"
        return "OPEN"

    def visible(self, mod):
        v = self.vis.get(mod)
        if v is None:
            seen = {mod}; st = [mod]
            while st:
                for x in self.imports.get(st.pop(), []):
                    if x not in seen: seen.add(x); st.append(x)
            v = self.vis[mod] = frozenset(seen)
        return v

    def toks(self, d):
        if d.tokens is None:
            text = d.text; sig, ty, _ = split_signature(text)
            local = set()
            for grp in BINDER_RE.findall(sig): local.update(grp.split())
            for grp in BINDER_RE.findall(ty): local.update(grp.split())
            for mm in LOCAL_RE.finditer(text):
                nm = mm.group(1); eol = text.find("\n", mm.end()); eol = len(text) if eol < 0 else eol
                if not re.search(r"(?<![\w.'])" + re.escape(nm) + r"(?![\w'])", text[mm.end():eol]): local.add(nm)
            for mm in LAMBDA_RE.finditer(text):
                local.update(x for x in re.findall(r"[^\W\d][\w'!?]*", mm.group(1)))
            local.update(NAMED_ARG_RE.findall(text)); local.update(FIELD_RE.findall(text))
            t = set(TOKEN_RE.findall(text))
            for gp in d.variables:
                inner = gp[1]; names = inner.split(":")[0].split() if ":" in inner else []
                if gp[0] == "[" or any(n in t for n in names):
                    t |= set(TOKEN_RE.findall(inner))
            d.tokens = (t - STOP, local)
        return d.tokens

    def resolve(self, tok, d, mod, vis):
        """All declarations tok can name from inside d."""
        if tok.startswith("_root_."): tok = tok[7:]
        chain = []
        for src in (d.ns, d.name.rsplit(".", 1)[0] if "." in d.name else ""):
            parts = src.split(".") if src else []
            for k in range(len(parts), 0, -1):
                p = ".".join(parts[:k])
                if p not in chain: chain.append(p)
        for p in chain:
            h = [x for m, x in self.names.get(p + "." + tok, ()) if m in vis]
            if h: return h
        hits = [x for m, x in self.names.get(tok, ()) if m in vis]
        for o in d.opens:
            for base in [o] + [p + "." + o for p in chain]:
                hits += [x for m, x in self.names.get(base + "." + tok, ()) if m in vis]
        return hits

    def refs(self, d):
        r = self.edges.get(d.name + "\0" + d.file)
        if r is not None: return r
        mod = self.module(d.file); vis = self.visible(mod); toks, local = self.toks(d)
        found = {}; tails = []
        for tok in toks:
            dotted = tok.startswith("."); t = tok.lstrip(".")
            head = t.split(".")[0]
            if dotted: tails.append(t); continue
            if head in local:
                if "." in t: tails.append(t.split(".", 1)[1])
                continue
            hit = self.resolve(t, d, mod, vis)
            if hit:
                for x in hit: found[id(x)] = x
                continue
            parts = t.split(".")
            got = False
            for k in range(len(parts) - 1, 0, -1):
                hit = self.resolve(".".join(parts[:k]), d, mod, vis)
                if hit:
                    for x in hit: found[id(x)] = x
                    tails.append(".".join(parts[k:])); got = True
                    break
            if not got and len(parts) > 1: tails.append(".".join(parts[1:]))
        direct = {x.name for x in found.values()}
        for t in tails:
            for suffix in {t, t.split(".")[-1]}:
                for m, x in self.tails.get(suffix, ()):
                    if m in vis and x.name[:-len(suffix) - 1] in direct: found[id(x)] = x
        # typeclass instances of classes this declaration mentions, sorry-bearing or native ones only matter
        for x in list(found.values()):
            if x.kind == "class":
                for m, inst in self.instances.get(x.name.split(".")[-1], ()):
                    if m in vis: found[id(inst)] = inst
        r = [x for x in found.values() if x is not d]
        self.edges[d.name + "\0" + d.file] = r
        return r

    def closure(self, d):
        seen = {id(d): (d, None)}; st = [d]
        while st:
            x = st.pop()
            for y in self.refs(x):
                if id(y) not in seen:
                    seen[id(y)] = (y, x); st.append(y)
        return seen

    def path(self, seen, d):
        out = []; cur = d
        while cur is not None:
            out.append(cur.name); cur = seen[id(cur)][1]
        return list(reversed(out))

    def find(self, name, folder=None):
        hits = [x for m, x in self.names.get(name, ())]
        if not hits and folder:
            hits = [x for x in self.folder_decls.get(folder, ()) if x.name == name or x.name.endswith("." + name)]
        if not hits:
            hits = [x for m, x in self.tails.get(name, ())]
        if folder:
            hits = sorted(hits, key=lambda x: x.folder != folder)
        return hits[0] if hits else None


def conditional(ix, d):
    """Statement hypotheses of d that are propositions, as short text."""
    sig, ty, _ = split_signature(d.text); out = []
    mod = ix.module(d.file); vis = ix.visible(mod)
    REL = re.compile(r"[≤<>≥=≠∀∃∈⊆∣¬∧∨↔]")
    def propish(t):
        t = t.strip()
        if REL.search(t): return True
        hd = TOKEN_RE.match(t)
        if not hd: return False
        for x in ix.resolve(hd.group(0), d, mod, vis):
            s = split_signature(x.text)
            if s[1].strip().endswith("Prop") or x.kind == "class" and "Prop" in s[1]: return True
        return False
    for op, inner in split_binders(sig):
        if op == "[" or ":" not in inner: continue
        t = inner.split(":", 1)[1].split(":=")[0]
        if propish(t): out.append(re.sub(r"\s+", " ", t.strip())[:60])
    depth = 0; last = 0; ty1 = ty
    parts = []
    for i, c in enumerate(ty1):
        if c in OPENERS: depth += 1
        elif c in CLOSERS: depth -= 1
        elif c == "→" and depth == 0: parts.append(ty1[last:i]); last = i + 1
        elif c in "∀∃" and depth == 0 and not ty1[last:i].strip(): break
    for t in parts:
        if propish(t): out.append(re.sub(r"\s+", " ", t.strip())[:60])
    seen = []
    for x in out:
        if x not in seen: seen.append(x)
    return seen


def is_prop_stmt(d):
    if d.kind not in ("def", "abbrev", "structure", "class"): return False
    return split_signature(d.text)[1].strip().endswith("Prop")


def measure(ix, d):
    seen = ix.closure(d)
    items = [x for x, _ in seen.values()]
    leaves = sorted({(x.name, x.cls) for x in items if x.sorry})
    op = sum(1 for _, c in leaves if c == "OPEN"); ci = sum(1 for _, c in leaves if c == "CITED")
    natives = sorted({x.name for x in items if x.native})
    refuted = sorted({x.name for x in items if x.sorry and x.name.split(".")[-1] in REFUTED})
    stub = d.sorry or is_prop_stmt(d)
    shown = [f"{n.replace('LeanLab.', '', 1)} {c}" for n, c in leaves]
    if is_prop_stmt(d) and not d.sorry:
        ci += 1; shown.insert(0, "UNPROVED Prop")
    return {"main": d.name, "open": op, "cited": ci, "total": op + ci, "stub": stub, "cond": conditional(ix, d), "leaves": shown,
            "native": natives, "refuted": refuted, "size": len(items), "file": os.path.relpath(d.file, ix.src), "line": d.line, "prop": is_prop_stmt(d)}


def auto_main(ix, folder):
    best = None
    for d in ix.folder_decls[folder]:
        if d.kind not in ("theorem", "lemma") or not d.named: continue
        seen = ix.closure(d)
        n = sum(1 for x, _ in seen.values() if x.folder == folder)
        if best is None or n > best[0] or (n == best[0] and d.name < best[1].name): best = (n, d)
    return best[1] if best else None


def rows_for(ix, mains_extra):
    table = collections.defaultdict(list)
    for f, n, m in CURATED: table[f].append((n, m))
    for f, n in mains_extra: table[f] = [(n, "curated")]
    rows = []
    for folder in sorted(os.listdir(ix.src)):
        if not os.path.isdir(os.path.join(ix.src, folder)) or folder == "old": continue
        if not ix.folder_decls.get(folder): continue
        cands = []
        for name, meth in table.get(folder, []):
            d = ix.find(name, folder)
            if d is not None: r = measure(ix, d); r["method"] = meth; cands.append(r)
            else: print(f"note: {folder} main {name} not found", file=sys.stderr)
        if not cands:
            d = auto_main(ix, folder)
            if d is None: continue
            r = measure(ix, d); r["method"] = "auto new" if folder not in table else "auto replaced"; cands.append(r)
        cands.sort(key=lambda r: (bool(r["refuted"]), r["stub"], r["total"], r["main"]))
        r = cands[0]; r["folder"] = folder; r["excluded"] = folder in EXCLUDED; r["hollow"] = HOLLOW.get(folder, "")
        r["local"] = len({x.name for x in ix.folder_decls[folder] if x.sorry})
        rows.append(r)
    return rows


def sort_key(r): return (r["total"], r["stub"], r["cited"], r["folder"])


def flags(r):
    fl = []
    if r["stub"]: fl.append("STUB main is itself sorry or unproved Prop")
    if r["cond"]: fl.append("CONDITIONAL on " + "; ".join(r["cond"]))
    if r.get("hollow"): fl.append("HOLLOW " + r["hollow"])
    if r["refuted"]: fl.append("REFUTED leaf " + ", ".join(r["refuted"]))
    if r["native"]: fl.append(f"NATIVE {len(r['native'])}")
    return "; ".join(fl).replace("|", "/")


def table(rows):
    out = ["| Rank | Folder | Main theorem | Sorries left | OPEN | CITED | Flags | Sorry declarations in closure | Folder local sorry | Method |", "|---|---|---|---|---|---|---|---|---|---|"]
    live = sorted([r for r in rows if not r["excluded"] and r["total"] > 0], key=sort_key)
    zero = sorted([r for r in rows if not r["excluded"] and r["total"] == 0], key=lambda r: (bool(r["cond"]), r["folder"]))
    excl = sorted([r for r in rows if r["excluded"]], key=lambda r: r["folder"])
    def row(rank, r):
        return f"| {rank} | {r['folder']} | {r['main']}{' Prop, no proof' if r['prop'] else ''} | {r['total']} | {r['open']} | {r['cited']} | {flags(r)} | {'; '.join(r['leaves'][:12])}{' ...' if len(r['leaves']) > 12 else ''} | {r['local']} | {r['method']} |"
    for i, r in enumerate(live, 1): out.append(row(i, r))
    for r in zero: out.append(row("zero", r))
    for r in excl: out.append(row("excluded", r))
    return "\n".join(out)


def finish_lines(rows, n=10):
    """Lowest closures that can honestly be finished: curated, no STUB, no HOLLOW, no refuted leaf."""
    ok = [r for r in rows if not r["excluded"] and r["total"] > 0 and not r["stub"] and not r.get("hollow") and not r["refuted"]
          and r["method"] == "curated"]
    return [f"- FINISH {r['folder']} {r['main']} {r['total']}" for r in sorted(ok, key=sort_key)[:n]]


def same_statement(ix, r):
    """Theorems of the folder with the conclusion of the main, as (total, open, cited, name)."""
    norm = lambda s: re.sub(r"\s+", " ", s).strip()
    d = ix.find(r["main"], r["folder"]); t = norm(split_signature(d.text)[1]); out = []
    for x in ix.folder_decls[r["folder"]]:
        if x is d or x.kind != "theorem" or not x.named or x.sorry: continue
        tt = norm(split_signature(x.text)[1])
        if tt == t or tt.split(".")[-1] == t.split(".")[-1]:
            m = measure(ix, x); out.append((m["total"], m["open"], m["cited"], x.name))
    return sorted(out)


def main():
    ap = argparse.ArgumentParser(description="FINISH ranking of paper folders, static closure of the main theorem")
    ap.add_argument("checkout"); ap.add_argument("--md"); ap.add_argument("--json")
    ap.add_argument("--main", action="append", default=[]); ap.add_argument("--explain", action="append", default=[])
    ap.add_argument("--candidates", action="store_true"); ap.add_argument("--finish", help="write the FINISH lines here")
    a = ap.parse_args()
    ix = Index(a.checkout)
    sc = collections.Counter(x.cls for x in {x.name + x.file: x for x in ix.decls}.values() if x.sorry)
    print(f"files {len(ix.imports)} declarations {len(ix.decls)} OPEN {sc['OPEN']} CITED {sc['CITED']}", file=sys.stderr)
    for n in a.explain:
        d = ix.find(n)
        if d is None: print("explain: not found", n); continue
        seen = ix.closure(d); r = measure(ix, d)
        print(f"{d.name} {r['file']}:{r['line']} closure {r['size']} decls, OPEN {r['open']} CITED {r['cited']}")
        for x, _ in seen.values():
            if x.sorry: print(f"  {x.cls} {x.name} {os.path.relpath(x.file, ix.src)}:{x.line}\n    via " + " > ".join(ix.path(seen, x)))
    if a.explain and not a.md and not a.json: return
    rows = rows_for(ix, [tuple(x.split("=", 1)) for x in a.main])
    if a.candidates:
        for r in sorted(rows, key=sort_key):
            if r["excluded"]: continue
            print(f"{r['folder']} {r['main']} {r['total']}")
            for c in same_statement(ix, r): print("   ", *c)
    if a.finish: open(a.finish, "w", encoding="utf8").write("\n".join(finish_lines(rows)) + "\n")
    if a.json: json.dump(rows, open(a.json, "w", encoding="utf8"), ensure_ascii=False, indent=1)
    t = table(rows)
    if a.md: open(a.md, "w", encoding="utf8").write(t + "\n")
    elif not a.json: print(t)


if __name__ == "__main__":
    main()

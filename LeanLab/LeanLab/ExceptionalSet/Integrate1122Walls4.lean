import LeanLab.ExceptionalSet.Integrate1122
import LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3
import LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3

/-!
Burst burst-20261122, session S67, branch claude/ExceptionalSet-wire4walls, stacked on
claude/ExceptionalSet-integrate1122, claude/ExceptionalSet-caseIIa_lemma3 and
claude/ExceptionalSet-caseIId_lemma3.
Source P0082, J. Brüdern and A. Perelli, Ann. Inst. Fourier 48 (1998), Theorem 1 page 354.

All three major arc cases of Lemma 7 that use P0082 Lemma 3, case ii a, case ii b and case ii d,
pages 363 and 364, now run on the single reading `DQCaseIIbP0082.BPLemma3Hyp`, with the
threshold `P₀` chosen after `θ` as on page 357. The stronger reading `BPLemma3CoprimeHyp` and
the bundled `CaseIIdMajorLowerHyp` drop out. Theorem 1 is CONDITIONAL ON four named citation
walls. No new definition, no sorry, no statement changed. AI wrote the Lean code. Binary Goldbach
is open.
-/

namespace LeanLab.ExceptionalSet.Integrate1122Walls4

open LeanLab.ExceptionalSet.BrudernPerelli1998 (Theorem1)

/-- P0082 page 354 Theorem 1, CONDITIONAL ON exactly four named citation walls:
`KarLemma1`, Vinogradov's mean value theorem as Karacuba 1971 page 243 states it;
`KarLemma2`, Vinogradov's Weyl sum estimate, Karacuba pages 243 and 244;
`Lemma2NoExcBP`, P0082 Lemma 2 page 357, from Montgomery and Vaughan 1975;
`BPLemma3Hyp`, P0082 Lemma 3 page 358 with displays 12 to 15, from Montgomery and Vaughan 1975
formulas 6.17, 6.19 and 7.1. -/
theorem theorem1_of_four_walls
    (hK1 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma1)
    (hK2 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.BPLemma3Hyp) :
    Theorem1 :=
  LeanLab.ExceptionalSet.Integrate1122.theorem1_of_karacuba_and_leaves
    (LeanLab.ExceptionalSet.U1539.KaracubaSplit.karacubaThm1Named_of_vinogradov hK1 hK2)
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_absent_selected_wired hL)
    (LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3.leaf_coprime_selected_of_lemma3 hL3)
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_prime_product_selected_wired
      (LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.prime_product_selected_of_lemma3 hL3))
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_near_zero_selected_wired
      (LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3.caseIIdMajorLowerHyp_of_lemma3 hL3))

open Filter in
/-- P0082 page 354: the exceptional set has density zero for each `1 < γ < 3/2`,
CONDITIONAL ON the same four named citation walls. -/
theorem densityZero_of_four_walls
    (hK1 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma1)
    (hK2 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.BPLemma3Hyp)
    {γ : ℝ} (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    Tendsto (fun N : ℕ => (LeanLab.ExceptionalSet.BrudernPerelli1998.Eγ γ N : ℝ) / N)
      atTop (nhds 0) :=
  LeanLab.ExceptionalSet.BrudernPerelli1998.densityZero_of_theorem1
    (theorem1_of_four_walls hK1 hK2 hL hL3) h1 h2

end LeanLab.ExceptionalSet.Integrate1122Walls4

#print axioms LeanLab.ExceptionalSet.Integrate1122Walls4.theorem1_of_four_walls
#print axioms LeanLab.ExceptionalSet.Integrate1122Walls4.densityZero_of_four_walls

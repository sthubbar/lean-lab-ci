/-
Wiring, CLOUD S25, burst-20261122, unit P1122-0113. P0082, J. Brüdern and A. Perelli, Goldbach
numbers in sparse sequences, Ann. Inst. Fourier 48 (1998) 353-378, page 354, Theorem 1, from
`Prep1122MainWire.theorem1_of_named_citation_walls` with its Erdős–Turán wall discharged by
`ETDQ4.erdosTuranDQ4_split`. CONDITIONAL ON five named citation walls. No sorry.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ExceptionalSet.Prep1122MainWire
import LeanLab.ExceptionalSet.ETDQ4Split

namespace LeanLab.ExceptionalSet.ETDQ4

/-- P0082 page 354 Theorem 1, exactly the type of
`Prep1122MainWire.theorem1_of_named_citation_walls`, CONDITIONAL ON exactly five named citation
walls: Karacuba, the nonexceptional major formula, the coprime major formula, the prime product
case and the near-zero major formula. The Erdős–Turán inequality is proved,
`erdosTuranDQ4_split`. -/
theorem theorem1_of_five_citation_walls
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hP : LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected.PrimeProductSelectedP0082)
    (hII : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.CaseIIdMajorLowerHyp) :
    LeanLab.ExceptionalSet.BrudernPerelli1998.Theorem1 :=
  LeanLab.ExceptionalSet.Prep1122MainWire.theorem1_of_named_citation_walls hK
    erdosTuranDQ4_split hL hL3 hP hII

end LeanLab.ExceptionalSet.ETDQ4

import LeanLab.ExceptionalSet.Prep1122MainWire
import LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082

/-!
WIRING, burst-20261122 session S31, units P1122-0125 and P1122-0126. P0082, Bruedern and
Perelli 1998, https://doi.org/10.5802/aif.1621, page 354 Theorem 1.

`Prep1122MainWire.theorem1_of_named_citation_walls` takes the wall `PrimeProductSelectedP0082`
of page 363 case ii b as one of six named inputs. `DQCaseIIbP0082.prime_product_selected_of_lemma3`
discharges that wall from Lemma 3 of page 358, `BPLemma3Hyp`, with display 21 and the singular
series bound proved. This file records the resulting conditional Theorem 1: the case ii b wall
is replaced by the Lemma 3 citation wall it was built on.

CONDITIONAL, never PROVED. AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Prep1122CaseIIbWire

open LeanLab.ExceptionalSet.BrudernPerelli1998 (Theorem1)

/-- P0082 page 354 Theorem 1, CONDITIONAL ON `KaracubaThm1Named`, `ErdosTuranDQ4`,
`Lemma2NoExcBP`, `BPLemma3CoprimeHyp`, `BPLemma3Hyp` and `CaseIIdMajorLowerHyp`. Same as
`Prep1122MainWire.theorem1_of_named_citation_walls` with the case ii b wall
`PrimeProductSelectedP0082` replaced by Lemma 3, page 358. -/
theorem theorem1_of_walls_lemma3
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3c : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.BPLemma3Hyp)
    (hII : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.CaseIIdMajorLowerHyp) :
    Theorem1 :=
  LeanLab.ExceptionalSet.Prep1122MainWire.theorem1_of_named_citation_walls hK hET hL hL3c
    (LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.prime_product_selected_of_lemma3 hL3) hII

end LeanLab.ExceptionalSet.Prep1122CaseIIbWire

#print axioms LeanLab.ExceptionalSet.Prep1122CaseIIbWire.theorem1_of_walls_lemma3

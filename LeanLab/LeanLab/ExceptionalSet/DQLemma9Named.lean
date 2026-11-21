/-
Assembly of `U1539.Lemma9`, P0082 Brudern and Perelli 1998, Lemma 9 page 368, proved in the
paper on page 370, CONDITIONAL ON the two named hypotheses only: `ErdosTuranDQ4`, used for
Lemma 4 page 359, and `KaracubaThm1Named`, used for Lemma 10 pages 370 to 371. No new LEAF:
the two Fourier leaves of DQLemma9Decisions and `LeafS1Case` are proved on main.
Not built in the prep run. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.DQLemma9Decisions
import LeanLab.ExceptionalSet.DQLemma4Decisions
import LeanLab.ExceptionalSet.DQLemma10S1

namespace LeanLab.ExceptionalSet.DQLemma9Named

open LeanLab.ExceptionalSet.U1539

/-- CONDITIONAL ON `ErdosTuranDQ4` and `KaracubaThm1Named` only. The type is the sealed
`Lemma9`, the type of `U1539.lemma9`. -/
theorem lemma9_of_named (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) : Lemma9 :=
  have h10 : Lemma10 := LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK
  LeanLab.ExceptionalSet.DQLemma9.lemma9_of_lemma10_lemma4 h10
    (LeanLab.ExceptionalSet.DQLemma4.lemma4_of_erdosTuran_lemma10 hET h10)

/-- CONDITIONAL ON `ErdosTuranDQ4` and `KaracubaThm1Named` only. -/
theorem lemma4_of_named (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) : Lemma4 :=
  LeanLab.ExceptionalSet.DQLemma4.lemma4_of_erdosTuran_lemma10 hET
    (LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK)

end LeanLab.ExceptionalSet.DQLemma9Named

#print axioms LeanLab.ExceptionalSet.DQLemma9Named.lemma9_of_named
#print axioms LeanLab.ExceptionalSet.DQLemma9Named.lemma4_of_named

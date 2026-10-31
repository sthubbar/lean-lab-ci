import LeanLab.LZCesaroShort.Theorem1PProved
import LeanLab.LZCesaroShort.Lemma6Proof

/-!
# The proved paper statements under their cited names

AI wrote this Lean code. Binary Goldbach is open.
The source is arXiv 1606.00869v2.
Lemma 7 and Lemma 8 are unconditional.
Theorems 1 and 2, Lemma 1 and Section 5 are conditional on RH only.
The legacy Props Theorem1 and Theorem2b keep their original types.
They are lab misreadings and are not asserted here.
Lemma3 remains a cited Prop with no unconditional proof in this folder.
-/

namespace LeanLab.LZCesaroShort

/-- Lemma 7 on page 7, from the existing unconditional proof. -/
theorem lz_lemma7 : Lemma7 := lz_lemma7_proved

/-- Lemma 8 on page 7, from the existing unconditional proof. -/
theorem lz_lemma8 : Lemma8 := lz_lemma8_proved

/-- Section 5 on pages 10 and 11, conditional on RH only. -/
theorem lz_sec5_rh : RiemannHypothesis → Sec5RH := lz_sec5_rh_proved

/-- Lemma 1 on page 3, in the nondegenerate lab form, conditional on RH only. -/
theorem lz_lemma1 : RiemannHypothesis → Lemma1 := lz_lemma1_proved

/-- Theorem 2 equation 2 on page 2, conditional on RH only. -/
theorem lz_theorem2a : RiemannHypothesis → Theorem2a := theorem2a_proved

/-- Theorem 1 as printed on page 2, conditional on RH only. -/
theorem lz_theorem1_printed : RiemannHypothesis → Theorem1P := theorem1P_proved

/-- Theorem 2 equation 3 as printed on page 2, conditional on RH only. -/
theorem lz_theorem2b_printed : RiemannHypothesis → Theorem2bP := theorem2bP_proved

end LeanLab.LZCesaroShort

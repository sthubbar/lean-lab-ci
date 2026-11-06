/-
The final elementary scale comparison of Montgomery and Vaughan 1975, page 368.
P0029 cites this proof in its pages 17 to 20.
Reuse the existing final_lower proof and discharge its logarithm condition eventually.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ExceptionalSet.MontgomeryVaughan1975
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LeanLab.BhowmikGrimmelt2026

open Filter

/-- The final scalar margin holds at every sufficiently large P and every positive X.
Source: Montgomery Vaughan page 368, last display before section 9.
This proves no bound on the location of a Siegel zero. -/
theorem eventual_secondary_margin405 :
    ∀ᶠ P : ℝ in atTop, ∀ X : ℝ, 0 < X →
      X * P ^ (-(1 / 3) : ℝ) < X * P ^ (-(1 / 4) : ℝ) / Real.log P := by
  have hb := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 12 by norm_num)).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with P hbound hP
  intro X hX
  apply LeanLab.ExceptionalSet.MV75.final_lower hX hP
  have hpow : 0 < P ^ (1 / 12 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hlog : Real.log P ≤ (1 / 2 : ℝ) * P ^ (1 / 12 : ℝ) := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, abs_of_pos hpow] using hbound
  linarith

/-- An explicit sufficient cutoff for the same scalar margin.
The cutoff is a derived helper constant and is not a printed paper constant. -/
theorem secondary_margin_explicit405 {P X : ℝ}
    (hP : (48 : ℝ) ^ 24 ≤ P) (hX : 0 < X) :
    X * P ^ (-(1 / 3) : ℝ) < X * P ^ (-(1 / 4) : ℝ) / Real.log P := by
  have hP1 : 1 < P := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 48 ^ 24) hP
  have hP0 : 0 < P := by linarith
  apply LeanLab.ExceptionalSet.MV75.final_lower hX hP1
  have hroot : 48 ≤ P ^ (1 / 24 : ℝ) := by
    have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 48 ^ 24) hP
      (by norm_num : (0 : ℝ) ≤ 1 / 24)
    have he : ((48 : ℝ) ^ 24) ^ (1 / 24 : ℝ) = 48 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 48)]
      norm_num
    rwa [he] at hh
  have hlog := Real.log_le_rpow_div hP0.le (by norm_num : (0 : ℝ) < 1 / 24)
  have hl : Real.log P ≤ 24 * P ^ (1 / 24 : ℝ) := by
    convert hlog using 1 <;> norm_num <;> ring
  have hp : P ^ (1 / 12 : ℝ) = (P ^ (1 / 24 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
    norm_num
  rw [hp]
  have hm := mul_nonneg (sub_nonneg.mpr hroot)
    (le_trans (by norm_num : (0 : ℝ) ≤ 48) hroot)
  nlinarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.eventual_secondary_margin405

#print axioms LeanLab.BhowmikGrimmelt2026.secondary_margin_explicit405

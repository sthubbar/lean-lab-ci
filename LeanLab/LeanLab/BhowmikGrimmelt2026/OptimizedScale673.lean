/-
The exact validity range of the optimized scale on P0029 page 27.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BhowmikGrimmelt2026

/-- With eta equal to R to minus one quarter, the scale condition has the printed range. -/
theorem optimized_scale_iff673 {X R : ℝ} (hX : 0 ≤ X) (hR : 0 < R) :
    10 * R ^ 2 ≤ R ^ (-(1 / 4) : ℝ) * X ↔ R ≤ (X / 10) ^ (4 / 9 : ℝ) := by
  have hp : 0 < R ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hR _
  have he : R ^ 2 * R ^ (1 / 4 : ℝ) = R ^ (9 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    norm_num
  have hbudget : (10 * R ^ 2 ≤ R ^ (-(1 / 4) : ℝ) * X) ↔
      R ^ (9 / 4 : ℝ) ≤ X / 10 := by
    rw [Real.rpow_neg hR.le, inv_mul_eq_div, le_div_iff₀ hp,
      mul_assoc, he, le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    constructor <;> intro h <;> nlinarith only [h]
  have hroot : (R ≤ (X / 10) ^ (4 / 9 : ℝ)) ↔ R ^ (9 / 4 : ℝ) ≤ X / 10 := by
    convert Real.le_rpow_inv_iff_of_pos hR.le
      (div_nonneg hX (by norm_num : (0 : ℝ) ≤ 10)) (by norm_num : (0 : ℝ) < 9 / 4) using 1 <;>
      norm_num
  exact hbudget.trans hroot.symm

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.optimized_scale_iff673

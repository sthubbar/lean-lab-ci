import Mathlib.Analysis.Real.Pi.Bounds

/-!
The height condition in P0014 page 43 Proposition 4.6.
This checks the regime descriptions of the assigned split.
The large shift hypothesis alone does not determine the active maximum branch.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Height457
open Real

/-- At shift two the split calls the shift large but the standing height is active.
Derived diagnostic for the height condition on page 43, preceding display 4.43.
-/
theorem large_shift_standing_height :
    (1 : ℝ) < |(2 : ℝ)| ∧
      4 * π ^ 2 * |(2 : ℝ)| < 100 ∧
      max (4 * π ^ 2 * |(2 : ℝ)|) 100 = 100 := by
  have hpi := mul_self_lt_mul_self pi_pos.le pi_lt_d2
  have hh : 4 * π ^ 2 * |(2 : ℝ)| < 100 := by
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  exact ⟨by norm_num, hh, max_eq_right hh.le⟩

end LeanLab.HelfgottMajor.Height457

#print axioms LeanLab.HelfgottMajor.Height457.large_shift_standing_height

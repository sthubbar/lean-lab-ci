import Mathlib

/-! Negative comparison for the attempted Mathlib replacement of the cited input on page 168.
AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.BoundLimits109
open Real

/-- The main coefficient of Mathlib's Chebyshev bound exceeds the required coefficient. -/
theorem coefficient_gap : (1.25506 : ℝ) < log 4 := by
  have hh := Real.log_two_gt_d9
  have he : log (4 : ℝ) = log 2 + log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul (by norm_num) (by norm_num)]
  linarith

/-- For N at least 3, Mathlib's explicit psi bound is larger than both desired bounds.
This compares the bounds and does not assert that either cited estimate is false. -/
theorem mathlib_bound_too_large (N : ℝ) (hN : 3 ≤ N) :
    1.25506 * N < log 4 * N + 2 * Real.sqrt N * log N ∧
      1.0012 * N < log 4 * N + 2 * Real.sqrt N * log N := by
  have hn : 0 < N := by linarith
  have hl : 0 ≤ log N := log_nonneg (by linarith)
  have hh := mul_lt_mul_of_pos_right coefficient_gap hn
  have ht : 0 ≤ 2 * Real.sqrt N * log N := by positivity
  constructor <;> nlinarith

end LeanLab.LiuWang2002.BoundLimits109

#print axioms LeanLab.LiuWang2002.BoundLimits109.coefficient_gap
#print axioms LeanLab.LiuWang2002.BoundLimits109.mathlib_bound_too_large

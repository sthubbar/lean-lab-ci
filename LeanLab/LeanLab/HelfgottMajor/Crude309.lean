import LeanLab.HelfgottMajor.Decomp269b

/-!
A negative test for the direct pointwise Mellin bound times zero count route.
Source P0014 page 38 after display 4.28 and pages 39 and 43, displays 4.30 and 4.42.
The paper explains that this route is weaker than the Cauchy Schwarz estimate.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Crude309
open Real

/-- The direct half moment times zero count budget exceeds the target low zero budget.
The source witness is q equal to one and T equal to 10 to the power eight.
This compares two upper bound expressions and does not refute the low zero estimate.
-/
theorem crude_count_budget_too_large :
    (2.337 * sqrt (100000000 : ℝ) * log 100000000 +
      21.817 * sqrt 100000000 + 74.38) <
      2.15581 * (100000000 / π * log (100000000 / (2 * π * exp 1)) +
        0.5 * log 100000000 + 17.7) := by
  have hlog : log (100000000 : ℝ) ≤ 396 := by
    have he : (100000000 : ℝ) = 100 ^ 4 := by norm_num
    rw [he, log_pow]
    norm_num only [Nat.cast_ofNat]
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100)
    linarith
  have hlog0 : 0 ≤ log (100000000 : ℝ) := log_nonneg (by norm_num)
  have hratio : 1 ≤ log (100000000 / (2 * π * exp 1)) := by
    apply (le_log_iff_exp_le (by positivity)).mpr
    rw [le_div_iff₀ (by positivity)]
    have he := exp_one_lt_d9
    have hp := pi_lt_four
    have he0 := exp_pos (1 : ℝ)
    have he3 : exp 1 < 3 := by linarith
    have h1 : exp 1 * (2 * π * exp 1) ≤ 2 * 4 * (3 : ℝ) ^ 2 := by
      calc
        exp 1 * (2 * π * exp 1) = (2 * π) * (exp 1) ^ 2 := by ring
        _ ≤ 8 * 9 := mul_le_mul (by linarith) (by nlinarith) (sq_nonneg _) (by norm_num)
        _ = _ := by norm_num
    linarith
  have hmain : (25000000 : ℝ) ≤ 100000000 / π *
      log (100000000 / (2 * π * exp 1)) := by
    have hd : (25000000 : ℝ) ≤ 100000000 / π := by
      apply (le_div_iff₀ pi_pos).mpr
      linarith [pi_lt_four]
    nlinarith [mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ 100000000 / π)]
  have hs : sqrt (100000000 : ℝ) = 10000 := by norm_num
  rw [hs]
  nlinarith

/-- The boundary term retained by correct absolute discrepancy bookkeeping exceeds the tail budget.
Source P0014 page 38 after display 4.28 and page 41 display 4.35, at q equal to one and T equal to 100.
The common positive exponential factor is cancelled. This is a negative result for the repair route.
-/
theorem boundary_budget_too_large :
    4.329 * log (100 / (2 * π)) < 4.226 * (0.5 * log (100 : ℝ) + 17.7) := by
  have hlog : (2 : ℝ) ≤ log 100 ∧ log 100 ≤ 18 := by
    have he : (100 : ℝ) = 10 ^ 2 := by norm_num
    rw [he, log_pow]
    norm_num only [Nat.cast_ofNat]
    have hupper := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    have hlower : (1 : ℝ) ≤ log 10 := by
      apply (le_log_iff_exp_le (by norm_num)).mpr
      linarith [exp_one_lt_d9]
    constructor <;> linarith
  have hquot : log (100 / (2 * π)) ≤ log (100 : ℝ) := by
    apply log_le_log (by positivity)
    apply div_le_self (by norm_num)
    linarith [pi_gt_three]
  nlinarith [hlog.1, hlog.2]

end LeanLab.HelfgottMajor.Crude309

/-
Richstein 2001 p. 1748 Section 7 and Riesel 1994 p. 82 display 3.25.
This is only the exponent of a conjectural heuristic, not a statement about primes.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Richstein2001

/-- Arithmetic for the exponent of Riesel's conjectural heuristic in display 3.25.
For the gap size in Richstein p. 1748 Section 7, its exponential lies strictly
between the displayed powers of ten. This asserts no result about prime gaps. -/
theorem riesel_gap_exponent :
    (10 : ℝ) ^ (14000000 : ℕ) < Real.exp (1.62 * Real.sqrt (4 * 10 ^ 14)) ∧
      Real.exp (1.62 * Real.sqrt (4 * 10 ^ 14)) < (10 : ℝ) ^ (14100000 : ℕ) := by
  have hs : Real.sqrt (4 * (10 : ℝ) ^ 14) = 20000000 := by
    rw [show 4 * (10 : ℝ) ^ 14 = 20000000 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 20000000)]
  have hlo : (2.3025850926 : ℝ) < Real.log 10 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hhi : Real.log 10 < (2.3025850934 : ℝ) := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  rw [hs]
  constructor
  · rw [← Real.exp_log (by positivity : (0 : ℝ) < 10 ^ (14000000 : ℕ)),
      Real.exp_lt_exp, Real.log_pow]
    push_cast
    linarith
  · rw [← Real.exp_log (by positivity : (0 : ℝ) < 10 ^ (14100000 : ℕ)),
      Real.exp_lt_exp, Real.log_pow]
    push_cast
    linarith

end LeanLab.Richstein2001

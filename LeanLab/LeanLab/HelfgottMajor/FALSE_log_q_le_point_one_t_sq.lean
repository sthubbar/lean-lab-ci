import Mathlib

/-!
Disproof of the leaf `log_q_le_point_one_t_sq` of `LeanLab/HelfgottMajor/DecompF1619.lean`.

That leaf states, for every nonzero natural `q` and every real `t` with `100 ≤ t`,
`log q ≤ 0.1 * t ^ 2`. Its own doc comment says that in the applications `q` is at most the
height, but the statement carries no such hypothesis, and the right side does not depend on `q`.
At `t = 100` the right side is `1000`, while `q = 3 ^ 1000` has `log q = 1000 * log 3 > 1000`.

This file imports only Mathlib, so it does not depend on the `sorry` it refutes.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.FalseLogQ1122
open Real

/-- `1 < log 3`, from `exp 1 < 2.7182818286 < 3`. -/
theorem one_lt_log_three : 1 < log (3 : ℝ) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- At `q = 3 ^ 1000` and `t = 100` the inequality of `log_q_le_point_one_t_sq` fails strictly. -/
theorem log_q_gt_at_witness :
    0.1 * (100 : ℝ) ^ 2 < Real.log ((3 ^ 1000 : ℕ) : ℝ) := by
  rw [Nat.cast_pow, Real.log_pow]
  have := one_lt_log_three
  push_cast
  nlinarith

/-- FALSE. The negation of the leaf `log_q_le_point_one_t_sq`, with its exact binders,
hypothesis and inequality. -/
theorem log_q_le_point_one_t_sq_false :
    ¬ ∀ (q : ℕ) [NeZero q] (t : ℝ), 100 ≤ t → Real.log (q : ℝ) ≤ 0.1 * t ^ 2 := by
  intro h
  have hw := @h (3 ^ 1000) ⟨pow_ne_zero _ (by norm_num)⟩ 100 le_rfl
  have hgt := log_q_gt_at_witness
  linarith

end LeanLab.HelfgottMajor.FalseLogQ1122

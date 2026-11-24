import LeanLab.HelfgottMajor.DecompF1605

/-!
Refutation of `Decomp269c.shell_series_le_expTailIntegral` of DecompF1605.lean, burst 20261122.
FalseShell669 already refutes the same inequality stated with `TailIntegral123.expTailIntegral`.
This file states the negation with the exact constant `Decomp269c.expTailIntegral` used by the
sealed leaf, so the refuted statement is the sealed one character for character.
The left side does not depend on T and its zeroth summand alone is 12800 at q one, while the
proved bound `Decomp269c.exp_integral_bound` puts the right side below 103 at T one hundred.
Intended source: P0014 page 41, display 4.35; the shell majorant is a lab step, not printed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ShellSeries
open Real

/-- The sealed statement of `shell_series_le_expTailIntegral` fails at q one and T one hundred. -/
theorem FALSE_feed1122_shell_series_le_expTailIntegral :
    ¬ ∀ (q : ℕ) [NeZero q] (T : ℝ) (_hT : 100 ≤ T),
      6400 * ((q : ℝ) + 1) * (∑' n : ℕ, (((n : ℝ) ^ 2 + 1) * Real.exp (-0.1598 * (n : ℝ)))) ≤
        Decomp269c.expTailIntegral q T := by
  intro h
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * exp (-0.1598 * (n : ℝ))) := by
    simpa [Nat.cast_pow] using
      Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 0.1598)
  have h0 : Summable (fun n : ℕ => exp (-0.1598 * (n : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 0
      (by norm_num : (0 : ℝ) < 0.1598)
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2 + 1) * exp (-0.1598 * (n : ℝ))) := by
    simpa [add_mul] using h1.add h0
  have hterm := hs.le_tsum 0 (fun n _ => by positivity)
  simp only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
    mul_zero, exp_zero, one_mul] at hterm
  have ht := Decomp269c.exp_integral_bound 1 100 le_rfl
  have ha : 1 ≤ (100 : ℝ) / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [pi_lt_four]
  have hl0 : 0 ≤ log ((100 : ℝ) / (2 * π)) := log_nonneg ha
  have hl : log ((100 : ℝ) / (2 * π)) ≤ 100 :=
    (log_le_sub_one_of_pos (by positivity)).trans (by
      have : (100 : ℝ) / (2 * π) ≤ 100 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [pi_gt_three]
      linarith)
  have he : exp (-0.1598 * (100 : ℝ)) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  norm_num only [Nat.cast_one, one_mul] at ht
  have htail : Decomp269c.expTailIntegral 1 100 ≤ 103 := by
    refine ht.trans ?_
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 1.0242))
      he (by positivity) (by positivity : (0 : ℝ) ≤ 1.0242 * 100)
    norm_num at hh
    linarith
  have hw := h 1 100 le_rfl
  simp only [Nat.cast_one, show (6400 : ℝ) * (1 + 1) = 12800 by norm_num] at hw
  nlinarith

end LeanLab.HelfgottMajor.Feed1122ShellSeries


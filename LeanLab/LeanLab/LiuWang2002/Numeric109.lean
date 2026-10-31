import LeanLab.LiuWang2002.Constants

/-! Elementary reductions for P0023 page 168. AI wrote the Lean code.
Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.Numeric109
open Real

/-- The monotonicity needed for display 6.5, page 168. -/
theorem exp_div_pow7_mono (x y : ℝ) (hx : 7 ≤ x) (hxy : x ≤ y) :
    exp x / x ^ 7 ≤ exp y / y ^ 7 := by
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := by linarith
  have hl := log_le_sub_one_of_pos (div_pos hyp hxp)
  rw [log_div hyp.ne' hxp.ne'] at hl
  have hl' : x * (log y - log x) ≤ y - x := by
    have := (le_div_iff₀ hxp).mp (show log y - log x ≤ (y - x) / x by
      convert hl using 1 <;> field_simp)
    nlinarith
  have hd : 0 ≤ log y - log x := sub_nonneg.mpr (log_le_log hxp hxy)
  have he : x - 7 * log x ≤ y - 7 * log y := by
    nlinarith [mul_nonneg (show 0 ≤ x - 7 by linarith) hd]
  have hh := exp_le_exp.mpr he
  have ex : exp (7 * log x) = x ^ 7 := by
    simpa [exp_log hxp] using exp_nat_mul (log x) 7
  have ey : exp (7 * log y) = y ^ 7 := by
    simpa [exp_log hyp] using exp_nat_mul (log y) 7
  simpa only [exp_sub, ex, ey] using hh

/-- A simple lower bound for log N in the nontrivial regime on page 168. -/
theorem log_ge_seven (N : ℝ) (hN : 6.36e12 ≤ N) : 7 ≤ log N := by
  have hNp : 0 < N := by linarith
  apply (le_log_iff_exp_le hNp).mpr
  have h7 : exp (7 : ℝ) < 3 ^ 7 := by
    have he : exp (7 : ℝ) = exp 1 ^ 7 := by simpa using exp_nat_mul (1 : ℝ) 7
    rw [he]
    have hh : exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    simpa using pow_lt_pow_left₀ hh (exp_pos 1).le (show (7 : ℕ) ≠ 0 by decide)
  norm_num at h7
  linarith

/-- Lower logarithm certificate for the small N cutoff on page 168. -/
theorem log_cutoff_lower : (29.481 : ℝ) ≤ log (6.36e12 : ℝ) := by
  apply (le_log_iff_exp_le (by norm_num)).mpr
  have he : exp 1 ≤ (2.7182818286 : ℝ) := Real.exp_one_lt_d9.le
  have h29 : exp (29 : ℝ) = exp 1 ^ 29 := by simpa using exp_nat_mul (1 : ℝ) 29
  have hs : exp (0.481 : ℝ) ≤ 1.617692 := by
    have h := Real.exp_bound' (x := (0.481 : ℝ)) (by norm_num) (by norm_num)
      (n := 14) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hp := pow_le_pow_left₀ (exp_pos 1).le he 29
  rw [show (29.481 : ℝ) = 29 + 0.481 by norm_num, exp_add, h29]
  calc exp 1 ^ 29 * exp 0.481 ≤ 2.7182818286 ^ 29 * 1.617692 :=
      mul_le_mul hp hs (exp_pos _).le (by positivity)
    _ ≤ 6.36e12 := by norm_num

end LeanLab.LiuWang2002.Numeric109

#print axioms LeanLab.LiuWang2002.Numeric109.exp_div_pow7_mono
#print axioms LeanLab.LiuWang2002.Numeric109.log_ge_seven

#print axioms LeanLab.LiuWang2002.Numeric109.log_cutoff_lower

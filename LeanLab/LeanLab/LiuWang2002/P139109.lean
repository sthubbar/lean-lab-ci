import Mathlib

/-! The two elementary constants after display 2.16 on page 139 of P0023.
AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.P139109
open Real Set

/-- A lower bound for the logarithm of 3.36 times 3100 cubed, page 139. -/
theorem log_parameter : (25.2 : ℝ) ≤ log (3.36 * (3100 : ℝ) ^ 3) := by
  apply (le_log_iff_exp_le (by norm_num)).mpr
  have h25 : exp (25 : ℝ) = exp 1 ^ 25 := by simpa using exp_nat_mul (1 : ℝ) 25
  have he := Real.exp_one_lt_d9.le
  have hp := pow_le_pow_left₀ (exp_pos 1).le he 25
  have hs : exp (0.2 : ℝ) ≤ 1.222 := by
    have hh := Real.exp_bound' (x := (0.2 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hh
    linarith
  rw [show (25.2 : ℝ) = 25 + 0.2 by norm_num, exp_add, h25]
  calc exp 1 ^ 25 * exp 0.2 ≤ 2.7182818286 ^ 25 * 1.222 :=
      mul_le_mul hp hs (exp_pos _).le (by positivity)
    _ ≤ _ := by norm_num

/-- The lower bound 0.9869 for the zero real part parameter, page 139. -/
theorem alpha_lower (L : ℝ) (hL : 3100 ≤ L) :
    (0.9869 : ℝ) ≤ 1 - 0.33 / log (3.36 * L ^ 3) := by
  have hp : (3100 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  have hl : 25.2 ≤ log (3.36 * L ^ 3) :=
    log_parameter.trans (log_le_log (by norm_num) (by nlinarith))
  have hlogp : 0 < log (3.36 * L ^ 3) := by linarith
  have hh : 0.33 / log (3.36 * L ^ 3) ≤ (0.0131 : ℝ) := by
    apply (div_le_iff₀ hlogp).mpr
    linarith
  linarith

/-- Convexity gives the monotonicity used immediately after display 2.16, page 139. -/
theorem one_sub_rpow_div_antitone (x a0 a : ℝ) (hx : 0 < x) (ha0 : 0 < a0) (ha : a0 ≤ a) :
    (1 - x ^ a) / a ≤ (1 - x ^ a0) / a0 := by
  have hap : 0 < a := ha0.trans_le ha
  have ht0 : 0 ≤ a0 / a := by positivity
  have ht1 : a0 / a ≤ 1 := (div_le_one hap).mpr ha
  have hh := (convexOn_rpow_left hx).2 (mem_univ a) (mem_univ (0 : ℝ))
    ht0 (sub_nonneg.mpr ht1) (show a0 / a + (1 - a0 / a) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, rpow_zero, mul_one] at hh
  have hc : a0 / a * a = a0 := by field_simp
  rw [hc] at hh
  have hm := mul_le_mul_of_nonneg_left hh hap.le
  have he : a * (a0 / a * x ^ a + (1 - a0 / a)) = a0 * x ^ a + a - a0 := by
    field_simp
    ring
  rw [he] at hm
  apply (div_le_div_iff₀ hap ha0).mpr
  nlinarith

/-- A coarse lower bound for log 1000 certifies the numerical factor on page 139. -/
theorem log_thousand : (6 : ℝ) ≤ log 1000 := by
  apply (le_log_iff_exp_le (by norm_num)).mpr
  have he : exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hh := pow_le_pow_left₀ (exp_pos 1).le he 6
  have heq : exp (6 : ℝ) = exp 1 ^ 6 := by simpa using exp_nat_mul (1 : ℝ) 6
  rw [← heq] at hh
  norm_num at hh
  linarith

/-- The numerical endpoint of the factor bound after display 2.16, page 139. -/
theorem factor_numeric : (1 - (0.001 : ℝ) ^ (0.9869 : ℝ)) / 0.9869 ≤ 1.0122 := by
  have hl : log (0.001 : ℝ) ≤ -6 := by
    have he : log (0.001 : ℝ) = -log 1000 := by
      rw [show (0.001 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, log_inv]
    rw [he]
    linarith [log_thousand]
  have heq : (0.001 : ℝ) ^ (0.9869 : ℝ) =
      0.001 * exp (-0.0131 * log (0.001 : ℝ)) := by
    rw [rpow_def_of_pos (by norm_num)]
    rw [show log (0.001 : ℝ) * 0.9869 = log 0.001 + (-0.0131 * log 0.001) by ring,
      exp_add, exp_log (by norm_num)]
  have hh := Real.add_one_le_exp (-0.0131 * log (0.001 : ℝ))
  rw [heq]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.9869)).mpr
  nlinarith

/-- The factor is at most 1.0122 throughout the real part range used on page 139. -/
theorem factor_bound (α : ℝ) (hα : 0.9869 ≤ α) :
    (1 - (0.001 : ℝ) ^ α) / α ≤ 1.0122 :=
  (one_sub_rpow_div_antitone 0.001 0.9869 α (by norm_num) (by norm_num) hα).trans factor_numeric

/-- Both displayed comparisons after display 2.16, page 139, combined. -/
theorem zero_factor (L α : ℝ) (hL : 3100 ≤ L)
    (hα : 1 - 0.33 / log (3.36 * L ^ 3) ≤ α) :
    (1 - (0.001 : ℝ) ^ α) / α ≤ 1.0122 :=
  factor_bound α ((alpha_lower L hL).trans hα)

end LeanLab.LiuWang2002.P139109

#print axioms LeanLab.LiuWang2002.P139109.log_parameter
#print axioms LeanLab.LiuWang2002.P139109.alpha_lower
#print axioms LeanLab.LiuWang2002.P139109.one_sub_rpow_div_antitone

#print axioms LeanLab.LiuWang2002.P139109.log_thousand
#print axioms LeanLab.LiuWang2002.P139109.factor_numeric
#print axioms LeanLab.LiuWang2002.P139109.factor_bound
#print axioms LeanLab.LiuWang2002.P139109.zero_factor

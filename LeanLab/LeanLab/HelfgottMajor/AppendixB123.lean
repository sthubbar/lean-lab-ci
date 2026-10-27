import LeanLab.HelfgottMajor.Prop411Lemma44

/-!
P0014 Appendix B, page 74, the norm used in displays B.29 and B.30.
AI wrote this Lean code. Binary Goldbach is open.
The norm here is written as the square root of its defining one-dimensional integral.
-/

namespace LeanLab.HelfgottMajor.AppendixB123
open Real MeasureTheory intervalIntegral Finset

/-- The polynomial part of an antiderivative for the squared norm integrand on page 74. -/
noncomputable def Q (t : ℝ) : ℝ :=
  t ^ 9 / 2 - 33 * t ^ 8 / 4 + 63 * t ^ 7 - 601 * t ^ 6 / 2 +
    2043 * t ^ 5 / 2 - 10599 * t ^ 4 / 4 + 10663 * t ^ 3 / 2 -
    31989 * t ^ 2 / 4 + 31989 * t / 4 - 31989 / 8

/-- The defining integral of the norm of h divided by sqrt t, display B.29 on page 74. -/
noncomputable def hNorm : ℝ :=
  sqrt (∫ t in (0 : ℝ)..2, t ^ 3 * (2 - t) ^ 6 * exp (2 * t - 1))

/-- The antiderivative differentiates to the squared norm integrand, page 74. -/
theorem primitive_deriv (t : ℝ) :
    HasDerivAt (fun t => Q t * exp (2 * t - 1))
      (t ^ 3 * (2 - t) ^ 6 * exp (2 * t - 1)) t := by
  have hp : HasDerivAt Q
      (9 * t ^ 8 / 2 - 66 * t ^ 7 + 441 * t ^ 6 - 1803 * t ^ 5 +
        10215 * t ^ 4 / 2 - 10599 * t ^ 3 + 31989 * t ^ 2 / 2 -
        31989 * t / 2 + 31989 / 4) t := by
    convert (((((((((((hasDerivAt_pow 9 t).div_const 2)).sub (((hasDerivAt_pow 8 t).const_mul 33).div_const 4)).add ((hasDerivAt_pow 7 t).const_mul 63)).sub (((hasDerivAt_pow 6 t).const_mul 601).div_const 2)).add (((hasDerivAt_pow 5 t).const_mul 2043).div_const 2)).sub (((hasDerivAt_pow 4 t).const_mul 10599).div_const 4)).add (((hasDerivAt_pow 3 t).const_mul 10663).div_const 2)).sub (((hasDerivAt_pow 2 t).const_mul 31989).div_const 4)).add (((hasDerivAt_id t).const_mul 31989).div_const 4)).sub_const (31989 / 8) using 1
    · funext y
      simp [Q]
    · norm_num
      ring
  have he : HasDerivAt (fun t : ℝ => exp (2 * t - 1)) (2 * exp (2 * t - 1)) t := by
    convert (((hasDerivAt_id t).const_mul 2).sub_const 1).exp using 1
    · funext y
      simp
    · simp
      ring
  convert hp.mul he using 1
  unfold Q
  ring

/-- The exact squared norm on page 74, below display B.29. -/
theorem integral_exact :
    (∫ t in (0 : ℝ)..2, t ^ 3 * (2 - t) ^ 6 * exp (2 * t - 1)) =
      31989 / (8 * exp 1) - 585 * exp 1 ^ 3 / 8 := by
  have hi : IntervalIntegrable
      (fun t : ℝ => t ^ 3 * (2 - t) ^ 6 * exp (2 * t - 1)) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ => t ^ 3 * (2 - t) ^ 6 * exp (2 * t - 1))).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt (fun t _ => primitive_deriv t) hi]
  norm_num [Q]
  rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, exp_nat_mul, exp_neg]
  ring

/-- A Taylor lower bound with enough digits for the cancellation on page 74. -/
theorem exp_one_lower : (2.718281828459 : ℝ) ≤ exp 1 := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 18
  norm_num [sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- The closed form on page 74 is at most the square of the printed norm bound. -/
theorem norm_square_bound :
    31989 / (8 * exp 1) - 585 * exp 1 ^ 3 / 8 ≤ (1.5023459 : ℝ) ^ 2 := by
  have he := exp_one_lower
  have hdiv : 31989 / (8 * exp 1) ≤ 31989 / (8 * 2.718281828459 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hpow : (2.718281828459 : ℝ) ^ 3 ≤ exp 1 ^ 3 :=
    pow_le_pow_left₀ (by norm_num) he 3
  have hn : 31989 / (8 * 2.718281828459 : ℝ) - 585 * 2.718281828459 ^ 3 / 8 ≤
      (1.5023459 : ℝ) ^ 2 := by norm_num
  linarith

/-- Appendix B page 74, the norm used to obtain display B.30. -/
theorem hNorm_bound : hNorm ≤ 1.5023459 := by
  unfold hNorm
  rw [integral_exact, sqrt_le_left (by norm_num)]
  exact norm_square_bound

/-- Display B.30 on page 74, its coefficient after division by sqrt 2. -/
theorem hNorm_coefficient : hNorm / sqrt 2 ≤ 1.062319 := by
  exact (div_le_div_of_nonneg_right hNorm_bound (sqrt_nonneg 2)).trans
    LeanLab.HelfgottMajor.Prop411Lemma44.b30_const

/-- The closed form for the norm of eta diamond times log t in display B.27, page 74. -/
noncomputable def diamondLogClosed : ℝ :=
  sqrt (sqrt π / 32 * (8 * (log 2) ^ 2 + 2 * eulerMascheroniConstant ^ 2 + π ^ 2 +
    8 * (eulerMascheroniConstant - 2) * log 2 - 8 * eulerMascheroniConstant))

/-- Display B.27 on page 74, its closed form is at most 0.3220301.
The identity with the weighted norm remains a separate analytic input.
-/
theorem diamondLogClosed_bound : diamondLogClosed ≤ 0.3220301 := by
  have hgL := LeanLab.Helfgott2013.GammaFine.gamma_gt_fine
  have hgU := LeanLab.Helfgott2013.GammaFine.gamma_lt_fine
  have hlL := log_two_gt_d9
  have hlU := log_two_lt_d9
  have hpL := pi_gt_d20
  have hpU := pi_lt_d20
  have hs : sqrt π ≤ 1.77245385091 := by
    rw [sqrt_le_left (by norm_num)]
    nlinarith
  let a := eulerMascheroniConstant + 2 * log 2 - 2
  have haL : -0.0364913394 ≤ a := by dsimp [a]; linarith
  have haU : a ≤ 0 := by dsimp [a]; linarith
  have ha2 : a ^ 2 ≤ (-0.0364913394 : ℝ) ^ 2 := by nlinarith
  have hp2 : π ^ 2 ≤ (3.14159265358979323847 : ℝ) ^ 2 := by nlinarith
  have hb : 2 * a ^ 2 + π ^ 2 - 8 ≤ 1.872267636792 := by
    norm_num at ha2 hp2 ⊢
    linarith
  have hform : 8 * (log 2) ^ 2 + 2 * eulerMascheroniConstant ^ 2 + π ^ 2 +
      8 * (eulerMascheroniConstant - 2) * log 2 - 8 * eulerMascheroniConstant =
      2 * a ^ 2 + π ^ 2 - 8 := by dsimp [a]; ring
  unfold diamondLogClosed
  rw [sqrt_le_left (by norm_num), hform]
  have hprod := mul_le_mul hb hs (sqrt_nonneg π) (by norm_num : (0 : ℝ) ≤ 1.872267636792)
  nlinarith

/-- Display B.28 on page 74, arithmetic with the cited Mellin norm bound 16.193918. -/
theorem etaPlus_log_closed_product :
    (16.193918 / (2 * π)) * diamondLogClosed ≤ 0.8299818 := by
  have hMh := LeanLab.HelfgottMajor.Prop411Lemma44.etaP_log.1
  have h0 : 0 ≤ diamondLogClosed := sqrt_nonneg _
  calc (16.193918 / (2 * π)) * diamondLogClosed ≤ 2.5773421 * 0.3220301 :=
      mul_le_mul hMh diamondLogClosed_bound h0 (by norm_num)
    _ ≤ 0.8299818 := LeanLab.HelfgottMajor.Prop411Lemma44.etaP_log.2

/-- A triangle-inequality budget is too large to discharge the book's sharper log norm input.
Book page 440, display 16.48. This is not a lower bound for the true norm.
-/
theorem p3_triangle_budget_gap : (0.276856 : ℝ) < 2 * sqrt (2 / π) * 1.39554 := by
  have hc : (0.7 : ℝ) < sqrt (2 / π) := by
    rw [lt_sqrt (by norm_num), lt_div_iff₀ pi_pos]
    nlinarith [pi_lt_four]
  nlinarith

end LeanLab.HelfgottMajor.AppendixB123

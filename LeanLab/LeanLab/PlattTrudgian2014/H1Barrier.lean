/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 Section 7 page 30, display 43 with h = 1.
The bounds below concern the method, not the truth of the paper's lambda values.
-/
import LeanLab.PlattTrudgian2014.LambdaBounds

namespace LeanLab.PlattTrudgian2014

/-- A tangent lower bound for log cosh, from convexity of exp. -/
theorem log_cosh_tangent {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (r ^ 2 - 1) / (r ^ 2 + 1) * (t - Real.log r) + Real.log (Real.cosh (Real.log r)) ≤
      Real.log (Real.cosh t) := by
  have hd : 0 < r ^ 2 + 1 := by positivity
  let a := r ^ 2 / (r ^ 2 + 1)
  let b := 1 / (r ^ 2 + 1)
  have ha : 0 ≤ a := div_nonneg (sq_nonneg r) hd.le
  have hb : 0 ≤ b := div_nonneg (by norm_num) hd.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp
  have hj := convexOn_exp.2 (Set.mem_univ (t - Real.log r))
    (Set.mem_univ (-(t - Real.log r))) ha hb hab
  have harg : a * (t - Real.log r) + b * -(t - Real.log r) =
      (r ^ 2 - 1) / (r ^ 2 + 1) * (t - Real.log r) := by dsimp [a, b]; ring
  simp only [smul_eq_mul, harg] at hj
  have hm := mul_le_mul_of_nonneg_right hj (Real.cosh_pos (Real.log r)).le
  have heq : (a * Real.exp (t - Real.log r) + b * Real.exp (-(t - Real.log r))) *
      Real.cosh (Real.log r) = Real.cosh t := by
    rw [Real.cosh_log hr, neg_sub, Real.exp_sub, Real.exp_sub, Real.exp_log hr,
      Real.cosh_eq, Real.exp_neg]
    dsimp [a, b]
    field_simp [hr.ne', hd.ne', Real.exp_ne_zero]
  rw [heq] at hm
  apply Real.exp_le_exp.mp
  rwa [Real.exp_add, Real.exp_log (Real.cosh_pos _), Real.exp_log (Real.cosh_pos _)]

theorem h1_uncond_all_parameters_insufficient {t : ℝ} (ht : 0 ≤ t) :
    t * 0.8594 - Real.log (Real.cosh t) < (109 / 154 : ℝ) * Real.log 2 := by
  have hh := log_cosh_tangent (r := 4) (by norm_num) t
  have hr : ((4 : ℝ) ^ 2 - 1) / (4 ^ 2 + 1) = 15 / 17 := by norm_num
  rw [hr] at hh
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [hlog4] at hh
  have hb := log_cosh_log_four_lower
  rw [hlog4] at hb
  have hl := Real.log_two_lt_d9
  nlinarith

theorem h1_GRH_all_parameters_insufficient {t : ℝ} (ht : 0 ≤ t) :
    t * 0.7163436 - Real.log (Real.cosh t) < (1 / 2 : ℝ) * Real.log 2 := by
  have hh := log_cosh_tangent (r := 5 / 2) (by norm_num) t
  have hr : (((5 / 2 : ℝ) ^ 2 - 1) / ((5 / 2) ^ 2 + 1)) = 21 / 29 := by norm_num
  rw [hr, Real.cosh_log (by norm_num : (0 : ℝ) < 5 / 2)] at hh
  rw [show ((5 / 2 : ℝ) + (5 / 2)⁻¹) / 2 = 29 / 20 by norm_num] at hh
  have hlog : Real.log (5 / 2) ≤ Real.log 2 + 1 / 4 := by
    rw [show (5 / 2 : ℝ) = 2 * (5 / 4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
    linarith
  have hb := Real.sum_range_le_log_div (x := (9 / 49 : ℝ)) (by norm_num) (by norm_num) 1
  norm_num at hb
  have hl := Real.log_two_lt_d9
  nlinarith

#print axioms log_cosh_tangent

#print axioms h1_uncond_all_parameters_insufficient

#print axioms h1_GRH_all_parameters_insufficient

end LeanLab.PlattTrudgian2014

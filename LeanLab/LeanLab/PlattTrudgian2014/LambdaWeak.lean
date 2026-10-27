/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 6 Section 3.
The two bounds here are weaker variants under new names.
They use LambdaOK with the repaired N to power minus c normalization.
-/
import LeanLab.PlattTrudgian2014.LambdaBounds

namespace LeanLab.PlattTrudgian2014

/-- Weaker unconditional bound from the elementary h = 1 exponential moment estimate. -/
theorem pt_lambda_uncond_h1 : LambdaOK (109 / 154) 0.8977 := by
  apply lambdaOK_of_cosh (a := 0.89769) (t := Real.log 4) (by norm_num)
    (by norm_num) (by norm_num) (Real.log_pos (by norm_num))
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [hlog4]
  have hh := log_cosh_log_four_upper
  rw [hlog4] at hh
  have hl := Real.log_two_gt_d9
  nlinarith

/-- Weaker bound at the exponent used under GRH. Its numerical proof uses no GRH input. -/
theorem pt_lambda_GRH_h1 : LambdaOK (1 / 2) 0.7938 := by
  apply lambdaOK_of_cosh (a := 0.79379) (t := Real.log 4) (by norm_num)
    (by norm_num) (by norm_num) (Real.log_pos (by norm_num))
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [hlog4]
  have hh := log_cosh_log_four_upper
  rw [hlog4] at hh
  have hl := Real.log_two_gt_d9
  nlinarith

#print axioms pt_lambda_uncond_h1
#print axioms pt_lambda_GRH_h1

end LeanLab.PlattTrudgian2014

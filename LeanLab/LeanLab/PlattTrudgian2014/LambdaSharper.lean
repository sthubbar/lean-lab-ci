/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 6 Section 3, weaker variants.
Rational interval certificates sharpen the elementary h = 1 method.
-/
import LeanLab.PlattTrudgian2014.LambdaThreshold

namespace LeanLab.PlattTrudgian2014

open Finset

set_option maxHeartbeats 1000000 in
theorem log_43_10_box :
    1.458615022 < Real.log (43 / 10) ∧ Real.log (43 / 10) < 1.458615024 := by
  have h := Real.sum_range_sub_log_div_le (x := (33 / 53 : ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

set_option maxHeartbeats 1000000 in
theorem log_1949_860_box :
    0.818139309 < Real.log (1949 / 860) ∧ Real.log (1949 / 860) < 0.818139311 := by
  have h := Real.sum_range_sub_log_div_le (x := (1089 / 2809 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

set_option maxHeartbeats 1000000 in
theorem log_20_7_box :
    1.049822124 < Real.log (20 / 7) ∧ Real.log (20 / 7) < 1.049822126 := by
  have h := Real.sum_range_sub_log_div_le (x := (13 / 27 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

set_option maxHeartbeats 1000000 in
theorem log_449_280_box :
    0.472233284 < Real.log (449 / 280) ∧ Real.log (449 / 280) < 0.472233285 := by
  have h := Real.sum_range_sub_log_div_le (x := (169 / 729 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem pt_lambda_uncond_h1_sharp : LambdaOK (109 / 154) 0.89726 := by
  apply lambdaOK_of_cosh (a := 0.8972599) (t := Real.log (43 / 10)) (by norm_num)
    (by norm_num) (by norm_num) (Real.log_pos (by norm_num))
  rw [Real.cosh_log (by norm_num : (0 : ℝ) < 43 / 10)]
  rw [show ((43 / 10 : ℝ) + (43 / 10)⁻¹) / 2 = 1949 / 860 by norm_num]
  have ht := log_43_10_box.1
  have hc := log_1949_860_box.2
  have hl := Real.log_two_lt_d9
  nlinarith

theorem pt_lambda_GRH_h1_sharp : LambdaOK (1 / 2) 0.77995 := by
  apply lambdaOK_of_cosh (a := 0.7799499) (t := Real.log (20 / 7)) (by norm_num)
    (by norm_num) (by norm_num) (Real.log_pos (by norm_num))
  rw [Real.cosh_log (by norm_num : (0 : ℝ) < 20 / 7)]
  rw [show ((20 / 7 : ℝ) + (20 / 7)⁻¹) / 2 = 449 / 280 by norm_num]
  have ht := log_20_7_box.1
  have hc := log_449_280_box.2
  have hl := Real.log_two_lt_d9
  nlinarith

theorem lambdaThreshold_uncond_h1_sharp : lambdaThreshold (109 / 154) ≤ 0.89726 :=
  lambdaThreshold_le (by norm_num) pt_lambda_uncond_h1_sharp

theorem lambdaThreshold_GRH_h1_sharp : lambdaThreshold (1 / 2) ≤ 0.77995 :=
  lambdaThreshold_le (by norm_num) pt_lambda_GRH_h1_sharp

#print axioms log_43_10_box
#print axioms log_1949_860_box
#print axioms log_20_7_box
#print axioms log_449_280_box

#print axioms pt_lambda_uncond_h1_sharp

#print axioms pt_lambda_GRH_h1_sharp

#print axioms lambdaThreshold_uncond_h1_sharp

#print axioms lambdaThreshold_GRH_h1_sharp

end LeanLab.PlattTrudgian2014

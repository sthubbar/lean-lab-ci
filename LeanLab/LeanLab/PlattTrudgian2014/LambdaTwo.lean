/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 6 Section 3, weaker variants.
These bounds use the proved h = 2 certificate and rational logarithm enclosures.
-/
import LeanLab.PlattTrudgian2014.BlockTwo
import LeanLab.PlattTrudgian2014.MomentLargeValues
import LeanLab.PlattTrudgian2014.LambdaThreshold

namespace LeanLab.PlattTrudgian2014

set_option maxHeartbeats 1000000 in
theorem log_15_4_box :
    1.321755839 < Real.log (15 / 4) ∧ Real.log (15 / 4) < 1.321755841 := by
  have h := Real.sum_range_sub_log_div_le (x := (11 / 19 : ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

set_option maxHeartbeats 1000000 in
theorem log_3743_960_box :
    1.360709423 < Real.log (3743 / 960) ∧ Real.log (3743 / 960) < 1.360709425 := by
  have h := Real.sum_range_sub_log_div_le (x := (2783 / 4703 : ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

set_option maxHeartbeats 1000000 in
theorem log_8_3_box :
    0.980829252 < Real.log (8 / 3) ∧ Real.log (8 / 3) < 0.980829254 := by
  have h := Real.sum_range_sub_log_div_le (x := (5 / 11 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

set_option maxHeartbeats 1000000 in
theorem log_319_144_box :
    0.795377802 < Real.log (319 / 144) ∧ Real.log (319 / 144) < 0.795377805 := by
  have h := Real.sum_range_sub_log_div_le (x := (175 / 463 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem twoBlockFactor_log {r : ℝ} (hr : 0 < r) :
    twoBlockFactor (Real.log r) = (r ^ 2 + 1 + 2 / r) / 4 := by
  unfold twoBlockFactor
  rw [show 2 * Real.log r = Real.log r + Real.log r by ring, Real.exp_add,
    Real.exp_log hr, Real.exp_neg, Real.exp_log hr]
  ring

theorem pt_lambda_uncond_h2 : LambdaOK (109 / 154) 0.88592 := by
  apply lambdaOK_of_block (h := 2) (a := 0.8859199) (t := Real.log (15 / 4))
    (F := twoBlockFactor (Real.log (15 / 4))) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Real.log_pos (by norm_num)) (BlockBound_two (Real.log_nonneg (by norm_num)))
  have hf : twoBlockFactor (Real.log (15 / 4)) = 3743 / 960 := by
    rw [twoBlockFactor_log (by norm_num : (0 : ℝ) < 15 / 4)]
    norm_num
  rw [hf]
  have ht := log_15_4_box.1
  have hF := log_3743_960_box.2
  have hl := Real.log_two_lt_d9
  nlinarith

theorem pt_lambda_GRH_h2 : LambdaOK (1 / 2) 0.75881 := by
  apply lambdaOK_of_block (h := 2) (a := 0.7588099) (t := Real.log (8 / 3))
    (F := twoBlockFactor (Real.log (8 / 3))) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Real.log_pos (by norm_num)) (BlockBound_two (Real.log_nonneg (by norm_num)))
  have hf : twoBlockFactor (Real.log (8 / 3)) = 319 / 144 := by
    rw [twoBlockFactor_log (by norm_num : (0 : ℝ) < 8 / 3)]
    norm_num
  rw [hf]
  have ht := log_8_3_box.1
  have hF := log_319_144_box.2
  have hl := Real.log_two_lt_d9
  nlinarith

theorem lambdaThreshold_uncond_h2 : lambdaThreshold (109 / 154) ≤ 0.88592 :=
  lambdaThreshold_le (by norm_num) pt_lambda_uncond_h2

theorem lambdaThreshold_GRH_h2 : lambdaThreshold (1 / 2) ≤ 0.75881 :=
  lambdaThreshold_le (by norm_num) pt_lambda_GRH_h2

#print axioms log_15_4_box
#print axioms log_3743_960_box
#print axioms log_8_3_box
#print axioms log_319_144_box

#print axioms twoBlockFactor_log

#print axioms pt_lambda_uncond_h2

#print axioms pt_lambda_GRH_h2

#print axioms lambdaThreshold_uncond_h2

#print axioms lambdaThreshold_GRH_h2

end LeanLab.PlattTrudgian2014

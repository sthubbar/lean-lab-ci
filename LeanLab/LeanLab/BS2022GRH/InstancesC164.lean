/- AI wrote the Lean code for CODEX task164.
A kernel checked arithmetic parameter instance for journal Lemma 8.
GRH remains an explicit unproved input. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC164b
import LeanLab.BS2022GRH.QG
import LeanLab.BS2022GRH.Lemma9M
namespace LeanLab.BS2022GRH.InstancesC164
open Real Finset Classical ChenThresholdGRH Decomp148a
/-- Bounds for the coefficient at the concrete bilinear parameter Y. -/
theorem q_bounds : (0.16 : ℝ) ≤ qG 1e36 ∧ qG 1e36 ≤ 0.63995 := by
  constructor
  · apply qG_ge (by norm_num)
    · rw [le_log_iff_exp_le (by norm_num)]
      linarith [exp_one_lt_d9]
    · norm_num
  · exact qG_le_all _ (by norm_num)
/-- The logarithm at Y is between one and one hundred. -/
theorem log_bounds : (1 : ℝ) ≤ log 1e36 ∧ log 1e36 ≤ 100 := by
  constructor
  · rw [le_log_iff_exp_le (by norm_num)]
    linarith [exp_one_lt_d9]
  · rw [log_le_iff_le_exp (by norm_num)]
    have h := exp_nat_ge 100
    norm_num at h
    norm_num
    linarith
/-- The balancing cutoff lies between 5 and ten million. -/
theorem cutoff_bounds : (5 : ℝ) ≤ cutoff 1e36 ∧ cutoff 1e36 ≤ 1e7 := by
  have hq := q_bounds
  have hl := log_bounds
  have h2 : 0.69 ≤ log (2 : ℝ) ∧ log (2 : ℝ) ≤ 1 := by
    constructor
    · linarith [log_two_gt_d9]
    · have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this ⊢
      linarith
  have hq0 : 0 < qG (1e36 : ℝ) := by linarith [hq.1]
  have hl0 : 0 < log (1e36 : ℝ) := by linarith [hl.1]
  have h20 : 0 < log (2 : ℝ) := by linarith [h2.1]
  have hd : 0 < 2 * log 2 * qG 1e36 * log 1e36 := by positivity
  have hc : 0 ≤ cutoff 1e36 := by unfold cutoff; positivity
  have he : cutoff 1e36 ^ 3 = (1e18 : ℝ) / (2 * log 2 * qG 1e36 * log 1e36) := by
    unfold cutoff
    rw [← rpow_natCast, ← rpow_mul (by positivity)]
    norm_num
  have hdL : 0.2 ≤ 2 * log 2 * qG 1e36 * log 1e36 := by
    have hA := mul_le_mul h2.1 hq.1 (by norm_num) (by linarith)
    have hB := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ log (1e36 : ℝ))
    nlinarith
  have hdU : 2 * log 2 * qG 1e36 * log 1e36 ≤ 128 := by
    calc (2 : ℝ) * log 2 * qG (1e36 : ℝ) * log (1e36 : ℝ)
        ≤ 2 * 1 * 0.63995 * 100 := by
          gcongr <;> linarith [h2.2, hq.2, hl.2]
      _ ≤ (128 : ℝ) := by norm_num
  constructor
  · apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 5) hc (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [he, le_div_iff₀ hd]
    norm_num
    nlinarith
  · apply (pow_le_pow_iff_left₀ hc (by norm_num : (0 : ℝ) ≤ 1e7) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [he, div_le_iff₀ hd]
    norm_num
    nlinarith
/-- Every arithmetic and coefficient guard of the existing Lemma8J holds at instance V.
This does not assert GRH or the bilinear estimate. -/
theorem lemma8_parameters :
    (∀ n : ℕ, ‖(0 : ℂ)‖ ≤ 1) ∧ (25 : ℝ) ≤ 25 ∧ (25 : ℝ) ≤ 1e36 ∧
    (25 : ℝ) ≤ 1e35 ∧ (1e35 : ℝ) < 1e36 ∧ (1 : ℝ) < 1e18 ∧
    (1e18 : ℝ) < √((25 : ℝ) * 1e36) ∧
    √((25 : ℝ) * 1e36) / 1e18 ≤ cutoff 1e36 ∧
    cutoff 1e36 ≤ min 1e18 (√(1e35 : ℝ)) ∧ Even (2 : ℤ) := by
  have hc := cutoff_bounds
  have hs : √((25 : ℝ) * 1e36) = 5e18 := by norm_num
  have hz : (1e7 : ℝ) ≤ √(1e35 : ℝ) := by
    rw [le_sqrt (by norm_num) (by norm_num)]
    norm_num
  simp only [hs]
  refine ⟨by simp, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_, by norm_num⟩
  · norm_num
    convert hc.1 using 1 <;> norm_num
  · exact le_min (hc.2.trans (by norm_num)) (hc.2.trans hz)
end LeanLab.BS2022GRH.InstancesC164
#print axioms LeanLab.BS2022GRH.InstancesC164.q_bounds
#print axioms LeanLab.BS2022GRH.InstancesC164.log_bounds
#print axioms LeanLab.BS2022GRH.InstancesC164.cutoff_bounds
#print axioms LeanLab.BS2022GRH.InstancesC164.lemma8_parameters

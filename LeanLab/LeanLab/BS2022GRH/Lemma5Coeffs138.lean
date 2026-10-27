/-
AI wrote this Lean code for CODEX task138, 2026-10-27.
P0021 journal Lemma 5 p. 1216 and Remark 1 p. 1230.
Only the elementary coefficient bounds are proved here.
The Mobius counting and weighted totient sums of Lemma 5 remain cited analytic inputs.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.ChenThresholdGRH
namespace LeanLab.BS2022GRH.Lemma5Coeffs138
open Real ChenThresholdGRH
/-- The coefficient M_mu in journal Lemma 5, p. 1216. -/
noncomputable def mMu (x : ℝ) : ℝ := 6 / π ^ 2 + 0.68 / √x

/-- Remark 1 p. 1230: M_mu is at most 0.608 once x is at least 10^8. -/
theorem mMu_le0608 (x : ℝ) (hx : 1e8 ≤ x) : mMu x ≤ 0.608 := by
  have hs : (10000 : ℝ) ≤ √x := by
    have h := Real.sqrt_le_sqrt hx
    norm_num at h
    exact h
  have hp : (3.14159 : ℝ) ≤ π := by linarith [Real.pi_gt_d6]
  have hp2 : (3.14159 : ℝ) ^ 2 ≤ π ^ 2 := by nlinarith [Real.pi_pos]
  have h1 : 6 / π ^ 2 ≤ (6 : ℝ) / 3.14159 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
  have h2 : 0.68 / √x ≤ (0.68 : ℝ) / 10000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  unfold mMu
  linarith

/-- The coefficient M_phi of Lemma 5 p. 1216 is at least one for x greater than one. -/
theorem one_le_Mphi (x : ℝ) (hx : 1 < x) : 1 ≤ Mphi x := by
  have hl : 0 < log x := log_pos hx
  have hx0 : 0 < x := by linarith
  unfold Mphi
  have h1 : 0 ≤ 1.333 / log x := by positivity
  have h2 : 0 ≤ 2.44 / (√x * log x) := by positivity
  have h3 : 0 ≤ 11 / (√x * log x ^ 2) := by positivity
  have hm : 0 ≤ min (2.44 / (√x * log x)) (11 / (√x * log x ^ 2)) := le_min h2 h3
  linarith

/-- An elementary bound for the coefficient M_phi in Lemma 5 p. 1216 at x at least 10^8. -/
theorem Mphi_le1073 (x : ℝ) (hx : 1e8 ≤ x) : Mphi x ≤ 1.073 := by
  have hx0 : 0 < x := by linarith
  have hs : (10000 : ℝ) ≤ √x := by
    have h := Real.sqrt_le_sqrt hx
    norm_num at h
    exact h
  have hl : (18.4 : ℝ) ≤ log x := by
    have hlog : (18.4 : ℝ) ≤ log 1e8 := by
      have h := Real.log_two_gt_d9
      have h5 := Real.log_five_gt_d9
      have heq : log (1e8 : ℝ) = 8 * (log 2 + log 5) := by
        rw [show (1e8 : ℝ) = (10 : ℝ) ^ 8 by norm_num, Real.log_pow, Real.log_ten_eq]
        norm_num
      rw [heq]
      linarith
    exact hlog.trans (log_le_log (by norm_num) hx)
  have h1 : 1.333 / log x ≤ (1.333 : ℝ) / 18.4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl
  have h2 : 2.44 / (√x * log x) ≤ (2.44 : ℝ) / (10000 * 18.4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  unfold Mphi
  have hm := min_le_left (2.44 / (√x * log x)) (11 / (√x * log x ^ 2))
  linarith
/-- Lemma 13 pp. 1230 and 1231 rounds the divisor error coefficient up to 0.85. -/
theorem divisor_error_coefficient : (0.608 : ℝ) * 1.3841 < 0.85 := by norm_num

end LeanLab.BS2022GRH.Lemma5Coeffs138

#print axioms LeanLab.BS2022GRH.Lemma5Coeffs138.mMu_le0608

#print axioms LeanLab.BS2022GRH.Lemma5Coeffs138.one_le_Mphi

#print axioms LeanLab.BS2022GRH.Lemma5Coeffs138.Mphi_le1073

#print axioms LeanLab.BS2022GRH.Lemma5Coeffs138.divisor_error_coefficient

/- AI wrote this Lean code for CODEX task406. Goldbach is open.
Compare the error denominators in journal p. 1216 Lemma 5
and Ramare 2019 p. 156 Theorem 3.1. PhiBridge406 retains the source inputs.
https://doi.org/10.4064/bc118-10 -/
import LeanLab.BS2022GRH.PhiBridge406

namespace LeanLab.BS2022GRH.Audit406
open Real Finset ChenThresholdGRH
noncomputable section

/-- Error term comparison for journal p. 1216 and Ramare p. 156.
The journal's logarithmic branch is smaller than the source square root branch. -/
theorem printed_log_error_lt_source (x : ℝ) (hx : exp 1 < x) :
    11 / (√x * log x) < 11 / √(x * log x) := by
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hlog : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hroot : 0 < √x := sqrt_pos.mpr hx0
  have hden : √(x * log x) < √x * log x := by
    rw [sqrt_mul hx0.le]
    exact mul_lt_mul_of_pos_left (sqrt_lt_self_iff.mpr hlog) hroot
  exact div_lt_div_of_pos_left (by norm_num) (by positivity) hden

/-- Above exp five the journal's logarithmic branch is below the coarse source branch.
Source pages are journal p. 1216 and Ramare p. 156. -/
theorem printed_log_error_lt_coarse (x : ℝ) (hx : exp 5 ≤ x) :
    11 / (√x * log x) < 2.44 / √x := by
  have hx0 : 0 < x := (exp_pos 5).trans_le hx
  have hlog : 5 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hroot : 0 < √x := sqrt_pos.mpr hx0
  apply (div_lt_div_iff₀ (mul_pos hroot (by linarith : 0 < log x)) hroot).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlog hroot.le]

/-- The printed error minimum is strictly below the direct source error minimum.
This compares error envelopes, not the actual reciprocal totient sum. -/
theorem printed_error_lt_source_error (x : ℝ) (hx : exp 5 ≤ x) :
    min (2.44 / √x) (11 / (√x * log x)) <
      min (2.44 / √x) (11 / √(x * log x)) := by
  have hx1 : exp 1 < x := (exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 5)).trans_le hx
  exact (min_le_right _ _).trans_lt
    (lt_min (printed_log_error_lt_coarse x hx) (printed_log_error_lt_source x hx1))

/-- The exact sealed Mphi bound is below the source envelope with rounded constant 1.333.
This uses the same rounded constant on both sides. PhiBridge406 separately
uses the true constant slack and the finite range to recover the journal bound. -/
theorem printed_mphi_lt_source_envelope (x : ℝ) (hx : exp 5 ≤ x) :
    Mphi x * log x < log x + 1.333 +
      min (2.44 / √x) (11 / √(x * log x)) := by
  rw [PhiBridge406.mphi_error_identity x (by
    have : (1 : ℝ) < exp 5 := one_lt_exp_iff.mpr (by norm_num)
    exact this.trans_le hx)]
  have h := printed_error_lt_source_error x hx
  linarith

end
end LeanLab.BS2022GRH.Audit406

#print axioms LeanLab.BS2022GRH.Audit406.printed_log_error_lt_source
#print axioms LeanLab.BS2022GRH.Audit406.printed_log_error_lt_coarse
#print axioms LeanLab.BS2022GRH.Audit406.printed_error_lt_source_error
#print axioms LeanLab.BS2022GRH.Audit406.printed_mphi_lt_source_envelope

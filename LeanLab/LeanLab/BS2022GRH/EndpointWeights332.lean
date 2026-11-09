/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Power savings for the endpoint specialization of journal display 31, p. 1240.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.LogWeights332

namespace LeanLab.BS2022GRH.EndpointWeights332
open Real ChenThresholdGRH LogWeights332

/-- The increasing part of the inverse qG weights after retaining square root decay.
Derived from journal p. 1240 display 31. -/
noncomputable def H (w : ℝ) : ℝ := 2 * log 2 * (qG (2 * w) * √w * log w)

/-- The retained coefficient is positive on the source endpoint range, display 31. -/
theorem H_pos (W : ℝ) (hW : 0 < W) (hL : 2750 ≤ log W) : 0 < H W := by
  have h25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hq := DecompC164b.qG_positive (2 * W) (by linarith)
  have hl : 0 < log W := by linarith
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  unfold H
  positivity

/-- The retained coefficient increases on the source endpoint range, display 31. -/
theorem H_monotone (W T : ℝ) (hW : 0 < W) (hL : 2750 ≤ log W) (hWT : W ≤ T) :
    H W ≤ H T := by
  exact mul_le_mul_of_nonneg_left (qG_sqrt_log_monotone W T hW hL hWT)
    (by positivity : 0 ≤ 2 * log (2 : ℝ))

/-- The first endpoint weight decreases while retaining both logarithmic factors.
Derived from the first line of journal display 31, p. 1240. -/
theorem first_weight_antitone (W T : ℝ) (hW : 0 < W)
    (hL : 2750 ≤ log W) (hWT : W ≤ T) :
    log T ^ (5 : ℕ) * log (2 * T) ^ (1 / 3 : ℝ) / T ^ (1 / 6 : ℝ) ≤
      log W ^ (5 : ℕ) * log (2 * W) ^ (1 / 3 : ℝ) / W ^ (1 / 6 : ℝ) := by
  have hT : 0 < T := hW.trans_le hWT
  have hlog := log_le_log hW hWT
  have hlW : 0 < log W := by linarith
  have hlT : 0 < log T := by linarith
  have hW1 : 1 < W := by linarith [log_le_sub_one_of_pos hW]
  have h2W1 : 1 < 2 * W := by linarith
  have hl2W : 0 < log (2 * W) := log_pos h2W1
  have hl2T : 0 < log (2 * T) := log_pos (by linarith)
  have h2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have hfirst := log_power_antitone W T 5 (1 / 12) hW1 hWT (by norm_num)
    (by norm_num) (by linarith)
  norm_num only [rpow_ofNat] at hfirst
  have hsecond := log_power_antitone (2 * W) (2 * T) (1 / 3) (1 / 12) h2W1
    (by gcongr) (by norm_num) (by norm_num)
    (by rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hW.ne']; linarith)
  rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT.le,
    mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hW.le] at hsecond
  have hs : log (2 * T) ^ (1 / 3 : ℝ) / T ^ (1 / 12 : ℝ) ≤
      log (2 * W) ^ (1 / 3 : ℝ) / W ^ (1 / 12 : ℝ) := by
    apply (mul_le_mul_iff_left₀ (inv_pos.mpr (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / 12 : ℝ)))).mp
    convert hsecond using 1 <;> field_simp <;> ring
  have hm := mul_le_mul hfirst hs (by positivity) (by positivity)
  have hid (v : ℝ) (hv : 0 < v) :
      (log v ^ (5 : ℕ) / v ^ (1 / 12 : ℝ)) *
        (log (2 * v) ^ (1 / 3 : ℝ) / v ^ (1 / 12 : ℝ)) =
        log v ^ (5 : ℕ) * log (2 * v) ^ (1 / 3 : ℝ) / v ^ (1 / 6 : ℝ) := by
    rw [div_mul_div_comm, ← rpow_add hv]
    norm_num
  simpa only [hid T hT, hid W hW] using hm

/-- The inverse two thirds weight retains a one third power saving.
Exact scalar identity for journal display 31, p. 1240. -/
theorem inverse_two_thirds_identity (W : ℝ) (hW : 0 < W) (hL : 2750 ≤ log W) :
    (2 * qG (2 * W) * log 2) ^ (-(2 / 3) : ℝ) /
      (W ^ (2 / 3 : ℝ) * log W ^ (2 / 3 : ℝ)) =
      H W ^ (-(2 / 3) : ℝ) / W ^ (1 / 3 : ℝ) := by
  have hl : 0 < log W := by linarith
  have h25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hq := DecompC164b.qG_positive (2 * W) (by linarith)
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hp : 0 < 2 * qG (2 * W) * log 2 := by positivity
  have hH := H_pos W hW hL
  have he : H W ^ (2 / 3 : ℝ) =
      (2 * qG (2 * W) * log 2) ^ (2 / 3 : ℝ) *
        W ^ (1 / 3 : ℝ) * log W ^ (2 / 3 : ℝ) := by
    unfold H
    rw [show 2 * log 2 * (qG (2 * W) * √W * log W) =
      (2 * qG (2 * W) * log 2) * √W * log W by ring,
      mul_rpow (by positivity) hl.le, mul_rpow hp.le (sqrt_nonneg W), sqrt_eq_rpow,
      ← rpow_mul hW.le]
    norm_num
  rw [rpow_neg hp.le, rpow_neg hH.le, he]
  have hpow : W ^ (2 / 3 : ℝ) = W ^ (1 / 3 : ℝ) * W ^ (1 / 3 : ℝ) := by
    rw [← rpow_add hW]; norm_num
  rw [hpow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The inverse five sixths weight retains a two thirds power saving.
Exact scalar identity for journal display 31, p. 1240. -/
theorem inverse_five_sixths_identity (W : ℝ) (hW : 0 < W) (hL : 2750 ≤ log W) :
    (2 * qG (2 * W) * log 2) ^ (-(1 / 3) : ℝ) /
      (W ^ (5 / 6 : ℝ) * log W ^ (1 / 3 : ℝ)) =
      H W ^ (-(1 / 3) : ℝ) / W ^ (2 / 3 : ℝ) := by
  have hl : 0 < log W := by linarith
  have h25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hq := DecompC164b.qG_positive (2 * W) (by linarith)
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hp : 0 < 2 * qG (2 * W) * log 2 := by positivity
  have hH := H_pos W hW hL
  have he : H W ^ (1 / 3 : ℝ) =
      (2 * qG (2 * W) * log 2) ^ (1 / 3 : ℝ) *
        W ^ (1 / 6 : ℝ) * log W ^ (1 / 3 : ℝ) := by
    unfold H
    rw [show 2 * log 2 * (qG (2 * W) * √W * log W) =
      (2 * qG (2 * W) * log 2) * √W * log W by ring,
      mul_rpow (by positivity) hl.le, mul_rpow hp.le (sqrt_nonneg W), sqrt_eq_rpow,
      ← rpow_mul hW.le]
    norm_num
  rw [rpow_neg hp.le, rpow_neg hH.le, he]
  have hpow : W ^ (5 / 6 : ℝ) = W ^ (1 / 6 : ℝ) * W ^ (2 / 3 : ℝ) := by
    rw [← rpow_add hW]; norm_num
  rw [hpow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end LeanLab.BS2022GRH.EndpointWeights332
#print axioms LeanLab.BS2022GRH.EndpointWeights332.H_pos
#print axioms LeanLab.BS2022GRH.EndpointWeights332.H_monotone
#print axioms LeanLab.BS2022GRH.EndpointWeights332.first_weight_antitone
#print axioms LeanLab.BS2022GRH.EndpointWeights332.inverse_two_thirds_identity
#print axioms LeanLab.BS2022GRH.EndpointWeights332.inverse_five_sixths_identity

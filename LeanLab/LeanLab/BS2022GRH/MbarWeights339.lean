/- AI wrote this Lean code for CODEX task339. Goldbach is open.
The three variable weights in display 31 on journal p. 1240.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.WeightedQ339

namespace LeanLab.BS2022GRH.MbarWeights339
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- The logarithmic one sixth power weight decreases on the large slice range.
Journal p. 1240 first line of display 31. -/
theorem log_weight_antitone (W T : ℝ) (hW : 0 < W) (hL : 2750 ≤ log W) (hWT : W ≤ T) :
    log (2 * T) ^ (1 / 3 : ℝ) / T ^ (1 / 6 : ℝ) ≤
      log (2 * W) ^ (1 / 3 : ℝ) / W ^ (1 / 6 : ℝ) := by
  have hT : 0 < T := hW.trans_le hWT
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog := log_le_log hW hWT
  have hl2W : 0 < log (2 * W) := by rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hW.ne']; linarith
  have hl2T : 0 < log (2 * T) := by rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne']; linarith
  have heW : exp (2 : ℝ) ≤ 2 * W := (le_log_iff_exp_le (by positivity)).mp
    (by rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hW.ne']; linarith)
  have heT : exp (2 : ℝ) ≤ 2 * T := heW.trans (by gcongr)
  have hm := log_div_sqrt_antitoneOn heW heT (by gcongr : 2 * W ≤ 2 * T)
  have hc := (div_le_div_iff₀ (sqrt_pos.mpr (by positivity : 0 < 2 * T))
    (sqrt_pos.mpr (by positivity : 0 < 2 * W))).mp hm
  simp only [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hc
  have hcross : log (2 * T) * √W ≤ log (2 * W) * √T := by
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < √2)).mp
    convert hc using 1 <;> ring
  have hratio : log (2 * T) / √T ≤ log (2 * W) / √W :=
    (div_le_div_iff₀ (sqrt_pos.mpr hT) (sqrt_pos.mpr hW)).mpr hcross
  have hid (v : ℝ) (hv : 0 < v) (hlv : 0 < log (2 * v)) :
      (log (2 * v) / √v) ^ (1 / 3 : ℝ) = log (2 * v) ^ (1 / 3 : ℝ) / v ^ (1 / 6 : ℝ) := by
    rw [div_rpow hlv.le (sqrt_nonneg v), sqrt_eq_rpow, ← rpow_mul hv.le] <;> norm_num
  have hh := rpow_le_rpow (div_nonneg hl2T.le (sqrt_nonneg T)) hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  simpa only [hid T hT hl2T, hid W hW hl2W] using hh

/-- The two thirds inverse qG weight decreases on the large slice range.
Journal p. 1240 third line of display 31. -/
theorem inverse_two_thirds_antitone (W T : ℝ) (hW : 0 < W) (hL : 2750 ≤ log W) (hWT : W ≤ T) :
    (2 * qG (2 * T) * log 2) ^ (-(2 / 3) : ℝ) / (T ^ (2 / 3 : ℝ) * log T ^ (2 / 3 : ℝ)) ≤
      (2 * qG (2 * W) * log 2) ^ (-(2 / 3) : ℝ) / (W ^ (2 / 3 : ℝ) * log W ^ (2 / 3 : ℝ)) := by
  have hT : 0 < T := hW.trans_le hWT
  have hlW : 0 < log W := by linarith
  have hlog := log_le_log hW hWT
  have hlT : 0 < log T := hlW.trans_le hlog
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hqW := DecompC164b.qG_positive (2 * W) (by linarith)
  have hqT := DecompC164b.qG_positive (2 * T) (by linarith)
  let K : ℝ → ℝ := fun v => 2 * log 2 * (qG (2 * v) * v * log v)
  have hKW : 0 < K W := by dsimp [K]; positivity
  have hK : K W ≤ K T := mul_le_mul_of_nonneg_left
    (WeightedQ339.qG_mul_log_monotone W T hW hL hWT) (by positivity)
  have hid (v : ℝ) (hv : 0 < v) (hlv : 0 < log v) (hqv : 0 < qG (2 * v)) :
      (2 * qG (2 * v) * log 2) ^ (-(2 / 3) : ℝ) / (v ^ (2 / 3 : ℝ) * log v ^ (2 / 3 : ℝ)) =
        K v ^ (-(2 / 3) : ℝ) := by
    have hp : 0 < 2 * qG (2 * v) * log 2 := by positivity
    have hk : 0 < K v := by dsimp [K]; positivity
    have he : K v ^ (2 / 3 : ℝ) =
        (2 * qG (2 * v) * log 2) ^ (2 / 3 : ℝ) * v ^ (2 / 3 : ℝ) * log v ^ (2 / 3 : ℝ) := by
      dsimp [K]
      rw [show 2 * log 2 * (qG (2 * v) * v * log v) =
          ((2 * qG (2 * v) * log 2) * v) * log v by ring,
        mul_rpow (by positivity) hlv.le, mul_rpow hp.le hv.le]
    rw [rpow_neg hp.le, rpow_neg hk.le, he]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid T hT hlT hqT, hid W hW hlW hqW]
  exact rpow_le_rpow_of_nonpos hKW hK (by norm_num)

/-- The five sixths inverse qG weight decreases on the large slice range.
Journal p. 1240 last line of display 31. -/
theorem inverse_five_sixths_antitone (W T : ℝ) (hW : 0 < W) (hL : 2750 ≤ log W) (hWT : W ≤ T) :
    (2 * qG (2 * T) * log 2) ^ (-(1 / 3) : ℝ) / (T ^ (5 / 6 : ℝ) * log T ^ (1 / 3 : ℝ)) ≤
      (2 * qG (2 * W) * log 2) ^ (-(1 / 3) : ℝ) / (W ^ (5 / 6 : ℝ) * log W ^ (1 / 3 : ℝ)) := by
  have hT : 0 < T := hW.trans_le hWT
  have hlW : 0 < log W := by linarith
  have hlog := log_le_log hW hWT
  have hlT : 0 < log T := hlW.trans_le hlog
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hqW := DecompC164b.qG_positive (2 * W) (by linarith)
  have hqT := DecompC164b.qG_positive (2 * T) (by linarith)
  let K : ℝ → ℝ := fun v => 2 * log 2 * (qG (2 * v) * v * log v)
  have hKW : 0 < K W := by dsimp [K]; positivity
  have hK : K W ≤ K T := mul_le_mul_of_nonneg_left
    (WeightedQ339.qG_mul_log_monotone W T hW hL hWT) (by positivity)
  have hid (v : ℝ) (hv : 0 < v) (hlv : 0 < log v) (hqv : 0 < qG (2 * v)) :
      (2 * qG (2 * v) * log 2) ^ (-(1 / 3) : ℝ) / (v ^ (5 / 6 : ℝ) * log v ^ (1 / 3 : ℝ)) =
        K v ^ (-(1 / 3) : ℝ) * v ^ (-(1 / 2) : ℝ) := by
    have hp : 0 < 2 * qG (2 * v) * log 2 := by positivity
    have hk : 0 < K v := by dsimp [K]; positivity
    have he : K v ^ (1 / 3 : ℝ) =
        (2 * qG (2 * v) * log 2) ^ (1 / 3 : ℝ) * v ^ (1 / 3 : ℝ) * log v ^ (1 / 3 : ℝ) := by
      dsimp [K]
      rw [show 2 * log 2 * (qG (2 * v) * v * log v) =
          ((2 * qG (2 * v) * log 2) * v) * log v by ring,
        mul_rpow (by positivity) hlv.le, mul_rpow hp.le hv.le]
    have hvpow : v ^ (5 / 6 : ℝ) = v ^ (1 / 3 : ℝ) * v ^ (1 / 2 : ℝ) := by
      rw [← rpow_add hv]
      congr 1
      ring
    rw [rpow_neg hp.le, rpow_neg hk.le, rpow_neg hv.le, he, hvpow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid T hT hlT hqT, hid W hW hlW hqW]
  exact mul_le_mul (rpow_le_rpow_of_nonpos hKW hK (by norm_num))
    (rpow_le_rpow_of_nonpos hW hWT (by norm_num))
    (rpow_nonneg hT.le _) (rpow_nonneg hKW.le _)

end
end LeanLab.BS2022GRH.MbarWeights339
#print axioms LeanLab.BS2022GRH.MbarWeights339.log_weight_antitone
#print axioms LeanLab.BS2022GRH.MbarWeights339.inverse_two_thirds_antitone
#print axioms LeanLab.BS2022GRH.MbarWeights339.inverse_five_sixths_antitone

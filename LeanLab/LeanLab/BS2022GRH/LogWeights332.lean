/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Scalar endpoint weights derived from journal display 31 to 33, pp. 1240 and 1241.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.WeightedQ339

namespace LeanLab.BS2022GRH.LogWeights332
open Real ChenThresholdGRH

/-- A positive power of log divided by a power decreases after its turning point.
Derived scalar comparison for journal p. 1241 display 33. -/
theorem log_power_antitone (X N k a : ℝ) (hX : 1 < X) (hXN : X ≤ N)
    (hk : 0 < k) (ha : 0 < a) (hstart : k / a ≤ log X) :
    log N ^ k / N ^ a ≤ log X ^ k / X ^ a := by
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := hX0.trans_le hXN
  have hLX : 0 < log X := log_pos hX
  have hLN : 0 < log N := log_pos (hX.trans_le hXN)
  have hm := Journal.mono_step ha hk hstart (log_le_log hX0 hXN)
  have hid (v : ℝ) (hv : 0 < v) (hl : 0 < log v) :
      log v ^ k / v ^ a = exp (-(a * log v - k * log (log v))) := by
    rw [rpow_def_of_pos hl, rpow_def_of_pos hv, ← exp_sub]
    congr 1
    ring
  rw [hid N hN0 hLN, hid X hX0 hLX]
  exact exp_le_exp.mpr (neg_le_neg hm)

/-- The sieve level increases under the logarithmic guard in display 25.
Derived scalar comparison for journal pp. 1239 to 1241. -/
theorem Dstar_monotone (X N A : ℝ) (hX : 1 < X) (hXN : X ≤ N)
    (hA : 0 < A + 1) (hstart : 2 * (A + 1) ≤ log X) :
    √X / log X ^ (A + 1) ≤ √N / log N ^ (A + 1) := by
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := hX0.trans_le hXN
  have hLX : 0 < log X := log_pos hX
  have hLN : 0 < log N := log_pos (hX.trans_le hXN)
  have hm := log_power_antitone X N (A + 1) (1 / 2) hX hXN hA
    (by norm_num) (by convert hstart using 1 <;> ring)
  rw [← sqrt_eq_rpow, ← sqrt_eq_rpow] at hm
  apply (div_le_div_iff₀ (rpow_pos_of_pos hLX _) (rpow_pos_of_pos hLN _)).mpr
  simpa only [mul_comm] using
    (div_le_div_iff₀ (sqrt_pos.mpr hN0) (sqrt_pos.mpr hX0)).mp hm

/-- qG at twice w times square root w times log w increases on the source domain.
This retains a power saving in the inverse qG weights of journal display 31. -/
theorem qG_sqrt_log_monotone (W T : ℝ) (hW : 0 < W)
    (hL : 2750 ≤ log W) (hWT : W ≤ T) :
    qG (2 * W) * √W * log W ≤ qG (2 * T) * √T * log T := by
  have hT : 0 < T := hW.trans_le hWT
  have hlW : 0 < log W := by linarith
  have hlT : 0 < log T := hlW.trans_le (log_le_log hW hWT)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hqT := DecompC164b.qG_positive (2 * T) (by linarith)
  let R : ℝ → ℝ := fun v => log v / (√2 * (log 2 + log v))
  have hR : R W ≤ R T := by
    dsimp [R]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_nonneg hl2.le (sub_nonneg.mpr (log_le_log hW hWT))
    have hs : 0 < √(2 : ℝ) := by positivity
    nlinarith only [hh, hs]
  have hF := WeightedQ339.weighted_q_monotone (2 * W) (2 * T) (by positivity)
    (by rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hW.ne']; linarith) (by gcongr)
  have hl2T : 0 < log (2 * T) := log_pos (by linarith [log_le_sub_one_of_pos hT])
  have hp := mul_le_mul hF hR (by dsimp [R]; positivity)
    (by positivity : 0 ≤ qG (2 * T) * √(2 * T) * log (2 * T))
  have hid (v : ℝ) (hv : 0 < v) (hlv : 0 < log v) :
      (qG (2 * v) * √(2 * v) * log (2 * v)) * R v = qG (2 * v) * √v * log v := by
    dsimp [R]
    rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), log_mul (by norm_num : (2 : ℝ) ≠ 0) hv.ne']
    field_simp [(by positivity : (√(2 : ℝ)) ≠ 0), (add_pos hl2 hlv).ne']
  rw [hid W hW hlW, hid T hT hlT] at hp
  exact hp

end LeanLab.BS2022GRH.LogWeights332
#print axioms LeanLab.BS2022GRH.LogWeights332.log_power_antitone
#print axioms LeanLab.BS2022GRH.LogWeights332.Dstar_monotone
#print axioms LeanLab.BS2022GRH.LogWeights332.qG_sqrt_log_monotone

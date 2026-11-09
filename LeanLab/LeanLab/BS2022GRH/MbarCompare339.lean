/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Full monotonicity in w of the printed mbar coefficient.
Journal p. 1240 after display 31.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.MbarWeights339
import LeanLab.BS2022GRH.Mbar339

namespace LeanLab.BS2022GRH.MbarCompare339
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- The complete printed mbar decreases in its third argument on the guarded range.
Journal p. 1240 after display 31. This transfers only w and keeps N and A fixed. -/
theorem mbar_antitone (N A W T : ℝ) (hN : 1 < N) (hW : 0 < W)
    (hL : 2750 ≤ log W) (hWT : W ≤ T) (hTcap : T ≤ √(N / 2))
    (hD : 1e8 ≤ √N / log N ^ (A + 1)) : mbarJ N A T ≤ mbarJ N A W := by
  have hN0 : 0 < N := by linarith
  have hLN : 0 < log N := log_pos hN
  have hT : 0 < T := hW.trans_le hWT
  have hlW : 0 < log W := by linarith
  have hlogWT := log_le_log hW hWT
  have hlT : 0 < log T := hlW.trans_le hlogWT
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hT25 : 25 ≤ T := hW25.trans hWT
  have hl2W : 0 < log (2 * W) := log_pos (by linarith)
  have hl2T : 0 < log (2 * T) := log_pos (by linarith)
  have hqW := DecompC164b.qG_positive W hW25
  have hqT := DecompC164b.qG_positive T hT25
  have hq2W := DecompC164b.qG_positive (2 * W) (by linarith)
  have hq2T := DecompC164b.qG_positive (2 * T) (by linarith)
  let P := log N ^ (A + 1)
  let D := √N / P
  have hP : 0 < P := rpow_pos_of_pos hLN _
  have hD1 : 1 < D := by change 1 < √N / log N ^ (A + 1); linarith
  have hD0 : 0 < D := by linarith
  have hlogD1 : 1 < log D := by
    rw [lt_log_iff_exp_lt hD0]
    change exp 1 < √N / log N ^ (A + 1)
    linarith [exp_one_lt_d9]
  have hllD : 0 < log (log D) := log_pos hlogD1
  have hlogD : log D = log (√N) - (A + 1) * log (log N) := by
    dsimp [D, P]
    rw [log_div (sqrt_pos.mpr hN0).ne' (rpow_pos_of_pos hLN _).ne', log_rpow hLN]
  have hMD : 0 ≤ 2 * Mphi D := by linarith [Lemma5Coeffs138.one_le_Mphi D hD1]
  have hPhiW := Mphi339.one_le_Mphi0 W hW hL
  have hPhiT := Mphi339.one_le_Mphi0 T hT (hL.trans hlogWT)
  have hPhi := Mphi339.Mphi0_antitone W T hW25 hWT (Mphi339.cutoff_gt_one_large W hW hL)
  let F : ℝ → ℝ := fun v => log (2 * v) ^ (1 / 3 : ℝ) / v ^ (1 / 6 : ℝ)
  let I2 : ℝ → ℝ := fun v => (2 * qG (2 * v) * log 2) ^ (-(2 / 3) : ℝ) /
    (v ^ (2 / 3 : ℝ) * log v ^ (2 / 3 : ℝ))
  let I3 : ℝ → ℝ := fun v => (2 * qG (2 * v) * log 2) ^ (-(1 / 3) : ℝ) /
    (v ^ (5 / 6 : ℝ) * log v ^ (1 / 3 : ℝ))
  let C1 := (2 * log 2) ^ (-(2 / 3) : ℝ) * 2 ^ (1 / 3 : ℝ) * P
  let C2 := P / log 2
  let C3 := 0.69205 * log N ^ (A + 2) / (2 * log (log D))
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  have hC3 : 0 ≤ C3 := by dsimp [C3]; positivity
  have hFW : 0 ≤ F W := by dsimp [F]; positivity
  have hFT : 0 ≤ F T := by dsimp [F]; positivity
  have hI2T : 0 ≤ I2 T := by dsimp [I2]; positivity
  have hI3T : 0 ≤ I3 T := by dsimp [I3]; positivity
  have hqpow : qG T ^ (1 / 3 : ℝ) ≤ qG W ^ (1 / 3 : ℝ) :=
    rpow_le_rpow hqT.le (DecompC164a.qG_antitone W T (by linarith) hWT) (by norm_num)
  have hF : F T ≤ F W := MbarWeights339.log_weight_antitone W T hW hL hWT
  have hbase : C1 * qG T ^ (1 / 3 : ℝ) * F T ≤ C1 * qG W ^ (1 / 3 : ℝ) * F W :=
    mul_le_mul (mul_le_mul_of_nonneg_left hqpow hC1) hF hFT
      (mul_nonneg hC1 (rpow_nonneg hqW.le _))
  have hfront : C1 * qG T ^ (1 / 3 : ℝ) * F T * (1 + Mphi0 T) ≤
      C1 * qG W ^ (1 / 3 : ℝ) * F W * (1 + Mphi0 W) :=
    mul_le_mul hbase (add_le_add le_rfl hPhi) (by linarith)
      (mul_nonneg (mul_nonneg hC1 (rpow_nonneg hqW.le _)) hFW)
  have hmid : C2 * (T ^ (-(1 / 2) : ℝ) + (2 * T / N) ^ (1 / 2 : ℝ)) ≤
      C2 * (W ^ (-(1 / 2) : ℝ) + (2 * W / N) ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left (Mbar339.middle_term_antitone N W T hN0 hW hWT hTcap) hC2
  have hI2 : I2 T ≤ I2 W := MbarWeights339.inverse_two_thirds_antitone W T hW hL hWT
  have hI3 : I3 T ≤ I3 W := MbarWeights339.inverse_five_sixths_antitone W T hW hL hWT
  have hsum : P * I2 T + C3 * I3 T ≤ P * I2 W + C3 * I3 W := add_le_add
    (mul_le_mul_of_nonneg_left hI2 hP.le) (mul_le_mul_of_nonneg_left hI3 hC3)
  have htail : Mphi0 T * (P * I2 T + C3 * I3 T) ≤ Mphi0 W * (P * I2 W + C3 * I3 W) :=
    mul_le_mul hPhi hsum (by positivity) (by linarith)
  have hid (v : ℝ) : mbarJ N A v = 2 * Mphi D *
      (2 / log 2 + C1 * qG v ^ (1 / 3 : ℝ) * F v * (1 + Mphi0 v) +
        C2 * (v ^ (-(1 / 2) : ℝ) + (2 * v / N) ^ (1 / 2 : ℝ)) +
        Mphi0 v * (P * I2 v + C3 * I3 v)) := by
    unfold mbarJ
    rw [← hlogD]
    dsimp [D, P, C1, C2, C3, F, I2, I3]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid T, hid W]
  apply mul_le_mul_of_nonneg_left _ hMD
  linarith only [hfront, hmid, htail]

/-- The complete printed mbar is nonnegative on the large endpoint domain.
Journal display 31 on pp. 1239 and 1240. -/
theorem mbar_nonneg (N A W : ℝ) (hN : 1 < N) (hW : 0 < W) (hL : 2750 ≤ log W)
    (hD : 1e8 ≤ √N / log N ^ (A + 1)) : 0 ≤ mbarJ N A W := by
  have hN0 : 0 < N := by linarith
  have hLN : 0 < log N := log_pos hN
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hlW : 0 < log W := by linarith
  have hl2W : 0 < log (2 * W) := log_pos (by linarith)
  have hqW := DecompC164b.qG_positive W hW25
  have hq2W := DecompC164b.qG_positive (2 * W) (by linarith)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hPhi0 : 0 < Mphi0 W := by linarith [Mphi339.one_le_Mphi0 W hW hL]
  have hD1 : 1 < √N / log N ^ (A + 1) := by linarith
  have hPhi : 0 < Mphi (√N / log N ^ (A + 1)) := by
    linarith [Lemma5Coeffs138.one_le_Mphi _ hD1]
  have hlogD1 : 1 < log (√N / log N ^ (A + 1)) := by
    rw [lt_log_iff_exp_lt (by positivity)]
    linarith [exp_one_lt_d9]
  have hgap : 0 < log (log (√N) - (A + 1) * log (log N)) := by
    have he : log (√N) - (A + 1) * log (log N) = log (√N / log N ^ (A + 1)) := by
      rw [log_div (sqrt_pos.mpr hN0).ne' (rpow_pos_of_pos hLN _).ne', log_rpow hLN]
    rw [he]
    exact log_pos hlogD1
  unfold mbarJ
  positivity

end
end LeanLab.BS2022GRH.MbarCompare339
#print axioms LeanLab.BS2022GRH.MbarCompare339.mbar_antitone
#print axioms LeanLab.BS2022GRH.MbarCompare339.mbar_nonneg

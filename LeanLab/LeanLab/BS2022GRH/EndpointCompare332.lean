/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Endpoint transfer for the normalized majorant with A at least four.
Derived scalar consequences of journal display 31 to 33, pp. 1240 and 1241.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Endpoint339
import LeanLab.BS2022GRH.EndpointWeights332

namespace LeanLab.BS2022GRH.EndpointCompare332
open Real ChenThresholdGRH LogWeights332 EndpointWeights332

/-- The normalized endpoint majorant with the powers of log separated.
Derived scalar rewriting of journal display 31, p. 1240. -/
noncomputable def normalizedMajorant (N A : ℝ) : ℝ :=
  2 * Mphi (√N / log N ^ (A + 1)) *
    (2 / log 2 / log N ^ (A - 4) +
      (2 * log 2) ^ (-(2 / 3) : ℝ) * 2 ^ (1 / 3 : ℝ) *
        qG (N ^ (1 / 8 : ℝ)) ^ (1 / 3 : ℝ) *
        (log N ^ (5 : ℕ) * log (2 * N ^ (1 / 8 : ℝ)) ^ (1 / 3 : ℝ) /
          (N ^ (1 / 8 : ℝ)) ^ (1 / 6 : ℝ)) * (1 + Mphi0 (N ^ (1 / 8 : ℝ))) +
      (log N ^ (5 : ℕ) / N ^ (1 / 16 : ℝ) +
        √2 * (log N ^ (5 : ℕ) / N ^ (7 / 16 : ℝ))) / log 2 +
      Mphi0 (N ^ (1 / 8 : ℝ)) *
        (H (N ^ (1 / 8 : ℝ)) ^ (-(2 / 3) : ℝ) *
          (log N ^ (5 : ℕ) / N ^ (1 / 24 : ℝ)) +
          0.69205 / 2 * H (N ^ (1 / 8 : ℝ)) ^ (-(1 / 3) : ℝ) *
            (log N ^ (6 : ℕ) / N ^ (1 / 12 : ℝ)) /
            log (log (√N / log N ^ (A + 1)))))

/-- Exact middle term at the eighth root endpoint, journal display 31.
The two powers are one sixteenth and seven sixteenths. -/
theorem middle_identity (N : ℝ) (hN : 0 < N) :
    (N ^ (1 / 8 : ℝ)) ^ (-(1 / 2) : ℝ) +
        (2 * N ^ (1 / 8 : ℝ) / N) ^ (1 / 2 : ℝ) =
      1 / N ^ (1 / 16 : ℝ) + √2 / N ^ (7 / 16 : ℝ) := by
  have he : (N ^ (1 / 8 : ℝ)) ^ (-(1 / 2) : ℝ) = 1 / N ^ (1 / 16 : ℝ) := by
    rw [← rpow_mul hN.le]
    norm_num
    rw [rpow_neg hN.le, one_div]
  rw [he, div_rpow (by positivity) hN.le,
    mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (rpow_nonneg hN.le _), ← rpow_mul hN.le]
  norm_num only [show (1 / 8 : ℝ) * (1 / 2) = 1 / 16 by norm_num]
  rw [← sqrt_eq_rpow]
  have hp : N ^ (1 / 2 : ℝ) = N ^ (1 / 16 : ℝ) * N ^ (7 / 16 : ℝ) := by
    rw [← rpow_add hN]; norm_num
  rw [hp]
  field_simp

/-- Exact normalization of the full endpoint majorant.
Journal pp. 1240 and 1241, displays 31 and 33. No estimate is assumed. -/
theorem majorant_normalization (N A : ℝ) (hN : 0 < N) (hL : 22000 ≤ log N) :
    mbarJ N A (N ^ (1 / 8 : ℝ)) / log N ^ (A - 4) = normalizedMajorant N A := by
  let z := N ^ (1 / 8 : ℝ)
  have hz : 0 < z := rpow_pos_of_pos hN _
  have hlz : 2750 ≤ log z := by dsimp [z]; rw [log_rpow hN]; linarith
  have hLN : 0 < log N := by linarith
  have hP : log N ^ (A + 1) = log N ^ (A - 4) * log N ^ (5 : ℕ) := by
    rw [← rpow_natCast, ← rpow_add hLN]; congr 1; ring
  have hP2 : log N ^ (A + 2) = log N ^ (A - 4) * log N ^ (6 : ℕ) := by
    rw [← rpow_natCast, ← rpow_add hLN]; congr 1; ring
  have hz2 : z ^ (1 / 3 : ℝ) = N ^ (1 / 24 : ℝ) := by
    dsimp [z]; rw [← rpow_mul hN.le]; norm_num
  have hz3 : z ^ (2 / 3 : ℝ) = N ^ (1 / 12 : ℝ) := by
    dsimp [z]; rw [← rpow_mul hN.le]; norm_num
  have hlogD : log (√N) - (A + 1) * log (log N) =
      log (√N / log N ^ (A + 1)) := by
    rw [log_div (sqrt_pos.mpr hN).ne' (rpow_pos_of_pos hLN _).ne', log_rpow hLN]
  have hi2 := inverse_two_thirds_identity z hz hlz
  have hi3 := inverse_five_sixths_identity z hz hlz
  have hmid := middle_identity N hN
  change mbarJ N A z / log N ^ (A - 4) = _
  unfold mbarJ normalizedMajorant
  rw [hlogD]
  have hr2 : (2 * qG (2 * z) * log 2) ^ (-(2 / 3) : ℝ) *
      (log N ^ (A + 1) / (z ^ (2 / 3 : ℝ) * log z ^ (2 / 3 : ℝ))) =
      log N ^ (A + 1) * (H z ^ (-(2 / 3) : ℝ) / N ^ (1 / 24 : ℝ)) := by
    rw [← hz2, ← hi2]; ring
  have hr3 : 0.69205 * (2 * qG (2 * z) * log 2) ^ (-(1 / 3) : ℝ) *
      (log N ^ (A + 2) / (2 * z ^ (5 / 6 : ℝ) * log z ^ (1 / 3 : ℝ) *
        log (log (√N / log N ^ (A + 1))))) =
      0.69205 / 2 * log N ^ (A + 2) *
        (H z ^ (-(1 / 3) : ℝ) / N ^ (1 / 12 : ℝ)) /
          log (log (√N / log N ^ (A + 1))) := by
    rw [← hz3, ← hi3]
    ring
  rw [hr2, hr3]
  change _ = _
  rw [show z ^ (-(1 / 2) : ℝ) + (2 * z / N) ^ (1 / 2 : ℝ) =
      1 / N ^ (1 / 16 : ℝ) + √2 / N ^ (7 / 16 : ℝ) from hmid]
  rw [hP, hP2]
  field_simp [(rpow_pos_of_pos hLN (A - 4)).ne']
  <;> ring

/-- The normalized endpoint majorant decreases for A at least four.
The logarithmic guard and the lower sieve level remain explicit.
Derived scalar endpoint step for journal p. 1241 display 33. -/
theorem normalizedMajorant_antitone (X N A : ℝ) (hX : 0 < X)
    (hLX : 22000 ≤ log X) (hXN : X ≤ N) (hA : 4 ≤ A)
    (hstart : 2 * (A + 1) ≤ log X) (hD : 1e8 ≤ √X / log X ^ (A + 1)) :
    normalizedMajorant N A ≤ normalizedMajorant X A := by
  have hN : 0 < N := hX.trans_le hXN
  have hlog := log_le_log hX hXN
  have hlX : 0 < log X := by linarith
  have hlN : 0 < log N := by linarith
  have hX1 : 1 < X := by linarith [log_le_sub_one_of_pos hX]
  have hN1 : 1 < N := hX1.trans_le hXN
  let W := X ^ (1 / 8 : ℝ)
  let T := N ^ (1 / 8 : ℝ)
  let DX := √X / log X ^ (A + 1)
  let DN := √N / log N ^ (A + 1)
  have hW : 0 < W := rpow_pos_of_pos hX _
  have hT : 0 < T := rpow_pos_of_pos hN _
  have hWL : 2750 ≤ log W := by dsimp [W]; rw [log_rpow hX]; linarith
  have hTL : 2750 ≤ log T := by dsimp [T]; rw [log_rpow hN]; linarith
  have hWT : W ≤ T := rpow_le_rpow hX.le hXN (by norm_num)
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hT25 : 25 ≤ T := hW25.trans hWT
  have hqW := DecompC164b.qG_positive W hW25
  have hqT := DecompC164b.qG_positive T hT25
  have hq : qG T ^ (1 / 3 : ℝ) ≤ qG W ^ (1 / 3 : ℝ) :=
    rpow_le_rpow hqT.le (DecompC164a.qG_antitone W T (by linarith) hWT) (by norm_num)
  have hphiW := Mphi339.one_le_Mphi0 W hW hWL
  have hphiT := Mphi339.one_le_Mphi0 T hT hTL
  have hphi := Mphi339.Mphi0_antitone W T hW25 hWT
    (Mphi339.cutoff_gt_one_large W hW hWL)
  have hDM : DX ≤ DN := Dstar_monotone X N A hX1 hXN (by linarith) hstart
  have hDX : 1 < DX := by dsimp [DX]; linarith
  have hDN : 1 < DN := hDX.trans_le hDM
  have hMD := Mphi339.Mphi_antitone DX DN hDX hDM
  have hMDX := Lemma5Coeffs138.one_le_Mphi DX hDX
  have hMDN := Lemma5Coeffs138.one_le_Mphi DN hDN
  have hLD : 1 < log DX := by
    rw [lt_log_iff_exp_lt (by linarith : 0 < DX)]
    dsimp [DX]
    linarith [exp_one_lt_d9]
  have hgapX : 0 < log (log DX) := log_pos hLD
  have hgap : log (log DX) ≤ log (log DN) :=
    log_le_log (by linarith) (log_le_log (by linarith) hDM)
  have hgapN : 0 < log (log DN) := hgapX.trans_le hgap
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hbase : 2 / log 2 / log N ^ (A - 4) ≤ 2 / log 2 / log X ^ (A - 4) := by
    apply div_le_div_of_nonneg_left (by positivity) (rpow_pos_of_pos hlX _)
    exact rpow_le_rpow hlX.le hlog (by linarith)
  have hscale (v : ℝ) (hv : 0 < v) :
      log v ^ (5 : ℕ) = 8 ^ (5 : ℕ) * log (v ^ (1 / 8 : ℝ)) ^ (5 : ℕ) := by
    rw [log_rpow hv]
    ring
  have hf := first_weight_antitone W T hW hWL hWT
  have hfirst : log N ^ (5 : ℕ) * log (2 * T) ^ (1 / 3 : ℝ) / T ^ (1 / 6 : ℝ) ≤
      log X ^ (5 : ℕ) * log (2 * W) ^ (1 / 3 : ℝ) / W ^ (1 / 6 : ℝ) := by
    rw [hscale N hN, hscale X hX]
    convert mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 8 ^ (5 : ℕ)) using 1 <;> ring
  have hl2W : 0 < log (2 * W) := log_pos (by linarith [log_le_sub_one_of_pos hW])
  have hl2T : 0 < log (2 * T) := log_pos (by linarith [log_le_sub_one_of_pos hT])
  have hfront := mul_le_mul
    (mul_le_mul
      (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤
        (2 * log 2) ^ (-(2 / 3) : ℝ) * 2 ^ (1 / 3 : ℝ)))
      hfirst (by positivity) (by positivity))
    (add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) hphi) (by linarith) (by positivity)
  have hmid1 := log_power_antitone X N 5 (1 / 16) hX1 hXN (by norm_num)
    (by norm_num) (by linarith)
  have hmid2 := log_power_antitone X N 5 (7 / 16) hX1 hXN (by norm_num)
    (by norm_num) (by linarith)
  have hmid := div_le_div_of_nonneg_right
    (add_le_add hmid1 (mul_le_mul_of_nonneg_left hmid2 (sqrt_nonneg (2 : ℝ)))) h2.le
  have hHW := H_pos W hW hWL
  have hHT := H_pos T hT hTL
  have hH := H_monotone W T hW hWL hWT
  have hinv2 := rpow_le_rpow_of_nonpos hHW hH (by norm_num : (-(2 / 3) : ℝ) ≤ 0)
  have hinv3 := rpow_le_rpow_of_nonpos hHW hH (by norm_num : (-(1 / 3) : ℝ) ≤ 0)
  have hdecay2 := log_power_antitone X N 5 (1 / 24) hX1 hXN (by norm_num)
    (by norm_num) (by linarith)
  have hdecay3 := log_power_antitone X N 6 (1 / 12) hX1 hXN (by norm_num)
    (by norm_num) (by linarith)
  norm_num only [rpow_ofNat] at hmid1 hmid2 hmid hdecay2 hdecay3
  have htail2 := mul_le_mul hinv2 hdecay2 (by positivity) (by positivity)
  have htail3 := div_le_div₀ (by positivity)
    (mul_le_mul (mul_le_mul_of_nonneg_left hinv3 (by norm_num : (0 : ℝ) ≤ 0.69205 / 2))
      hdecay3 (by positivity) (by positivity)) hgapX hgap
  have htail := mul_le_mul hphi (add_le_add htail2 htail3) (by positivity) (by linarith)
  unfold normalizedMajorant
  apply mul_le_mul (by linarith only [hMD]) _ _ (by linarith only [hMDX])
  · exact add_le_add (add_le_add (add_le_add hbase hfront) hmid) htail
  · positivity

/-- The full endpoint error transfers when A is at least four.
Derived scalar step after journal display 33, p. 1241.
This statement covers the existing restricted leaf and does not change positive A. -/
theorem error_at_threshold (α A u X₂ N ε₁ : ℝ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hAge : 4 ≤ A) (hc : Cond25 α A u X₂)
    (hX : exp (exp 10) ≤ X₂) (hN : X₂ ≤ N) :
    DecompC164c.errorBracket A N ε₁ ≤ DecompC164c.errorBracket A X₂ ε₁ := by
  have hX0 : 0 < X₂ := (exp_pos _).trans_le hX
  have hN0 : 0 < N := hX0.trans_le hN
  have hLX : 22000 ≤ log X₂ := Lemma11C164.log_lower X₂ hX
  have hLN : 22000 ≤ log N := hLX.trans (log_le_log hX0 hN)
  have hX1 : 1 < X₂ := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX
  have hstart : 2 * (A + 1) ≤ log X₂ := by
    have hfirst := (le_max_left ((A + 1) / α) (48 * (A + 4 / 3))).trans hc.1
    have hh := (div_le_iff₀ hα).mp hfirst
    have hlogpos : 0 < log X₂ := by linarith
    nlinarith
  have hD : 1e8 ≤ √X₂ / log X₂ ^ (A + 1) := by
    have h19 : exp u ≤ X₂ ^ α / log X₂ ^ (A + 1) := hc.2.1
    have hh := Journal.remark1_H hX1.le (by linarith : α ≤ 1 / 2)
      (rpow_pos_of_pos (log_pos hX1) (A + 1)) hc.2.2.2.1 h19
    norm_num at hh ⊢
    exact hh
  apply Endpoint339.error_transfer X₂ N A ε₁ hX1 (by linarith) hN hε
  rw [majorant_normalization N A hN0 hLN, majorant_normalization X₂ A hX0 hLX]
  exact normalizedMajorant_antitone X₂ N A hX0 hLX hN hAge hstart hD

end LeanLab.BS2022GRH.EndpointCompare332
#print axioms LeanLab.BS2022GRH.EndpointCompare332.middle_identity
#print axioms LeanLab.BS2022GRH.EndpointCompare332.majorant_normalization

#print axioms LeanLab.BS2022GRH.EndpointCompare332.normalizedMajorant_antitone
#print axioms LeanLab.BS2022GRH.EndpointCompare332.error_at_threshold

/- AI wrote this Lean code for CODEX task339. Goldbach is open.
A smaller scalar supply unit for display 31 on pp. 1239 and 1240.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Scale339
import LeanLab.BS2022GRH.SliceInstances236

namespace LeanLab.BS2022GRH.Decomp339c
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- LEAF. Compare only the printed coefficients before scale normalization.
Journal pp. 1239 and 1240 display 31, with W at most Y at most twice W.
This has no scale factor, slice sum, GRH input or endpoint transfer. -/
theorem rectangle_coefficient_bound (N W Y A : ℝ) (hN : 1 < N)
    (hW : 0 < W) (hLW : 2750 ≤ log W) (hWY : W ≤ Y) (hY2W : Y ≤ 2 * W)
    (hA : 0 < A) (hLN : 1 ≤ log N)
    (hD : 1e8 ≤ √N / log N ^ (A + 1)) :
    Decomp148a.mJ (N / W) Y (√N / log N ^ (A + 1)) ≤ mbarJ N A W := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < log N := log_pos hN
  have hY : 0 < Y := hW.trans_le hWY
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hY25 : 25 ≤ Y := hW25.trans hWY
  have hlW : 0 < log W := by linarith
  have hlY : 0 < log Y := log_pos (by linarith)
  have hl2W : 0 < log (2 * W) := log_pos (by linarith)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hqW := DecompC164b.qG_positive W hW25
  have hqY := DecompC164b.qG_positive Y hY25
  have hq2W := DecompC164b.qG_positive (2 * W) (by linarith)
  have hqWY := DecompC164a.qG_antitone W Y (by linarith) hWY
  have hqY2W := DecompC164a.qG_antitone Y (2 * W) (by linarith) hY2W
  have hlWY := log_le_log hW hWY
  have hlY2W := log_le_log hY hY2W
  let P := log N ^ (A + 1)
  let D := √N / P
  have hP : 0 < P := rpow_pos_of_pos hL _
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hlD : 0 ≤ log D := log_nonneg (by change 1 ≤ √N / log N ^ (A + 1); linarith)
  have hlD1 : 1 < log D := by
    rw [lt_log_iff_exp_lt hD0]
    change exp 1 < √N / log N ^ (A + 1)
    linarith [exp_one_lt_d9]
  have hllD : 0 < log (log D) := log_pos hlD1
  have hlogD : log D = log (√N) - (A + 1) * log (log N) := by
    dsimp [D, P]
    rw [log_div (sqrt_pos.mpr hN0).ne' (rpow_pos_of_pos hL _).ne', log_rpow hL]
  have hlDu : log D ≤ log N / 2 := by
    rw [hlogD, log_sqrt hN0.le]
    have := log_nonneg hLN
    nlinarith
  have hPhiW := Mphi339.one_le_Mphi0 W hW hLW
  have hPhiY := Mphi339.one_le_Mphi0 Y hY (hLW.trans hlWY)
  have hPhi := Mphi339.Mphi0_antitone W Y hW25 hWY (Mphi339.cutoff_gt_one_large W hW hLW)
  have hMD : 0 ≤ Mphi D := by
    have hd1 : 1 < D := by change 1 < √N / log N ^ (A + 1); linarith
    linarith [Lemma5Coeffs138.one_le_Mphi D hd1]
  have hroot : (N / W) ^ (1 / 2 : ℝ) / D = P / W ^ (1 / 2 : ℝ) := by
    rw [div_rpow hN0.le hW.le, ← sqrt_eq_rpow]
    dsimp [D]
    field_simp
  have hpow (a b : ℝ) : W ^ a * W ^ b = W ^ (a + b) := (rpow_add hW a b).symm
  have hPnext : P * log N = log N ^ (A + 2) := by
    dsimp [P]
    calc _ = log N ^ (A + 1) * log N ^ (1 : ℝ) := by rw [rpow_one]
         _ = _ := by rw [← rpow_add hL]; congr 1; ring
  let B := qG W ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) *
    (2 ^ (1 / 3 : ℝ) * P * log (2 * W) ^ (1 / 3 : ℝ) / W ^ (1 / 6 : ℝ))
  let S := (2 * qG (2 * W) * log 2) ^ (-(2 / 3) : ℝ) *
    (P / (W ^ (2 / 3 : ℝ) * log W ^ (2 / 3 : ℝ)))
  let T := 0.69205 * (2 * qG (2 * W) * log 2) ^ (-(1 / 3) : ℝ) *
    (log N ^ (A + 2) / (2 * W ^ (5 / 6 : ℝ) * log W ^ (1 / 3 : ℝ) * log (log D)))
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hbal : Decomp148a.balance (N / W) Y D ≤ B := by
    unfold Decomp148a.balance
    have hid : (N / W) ^ (1 / 2 : ℝ) * Y ^ (1 / 3 : ℝ) * log Y ^ (1 / 3 : ℝ) / D =
        P / W ^ (1 / 2 : ℝ) * Y ^ (1 / 3 : ℝ) * log Y ^ (1 / 3 : ℝ) := by
      rw [← hroot]
      ring
    rw [hid]
    calc _ ≤ qG W ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) *
        (P / W ^ (1 / 2 : ℝ) * (2 * W) ^ (1 / 3 : ℝ) * log (2 * W) ^ (1 / 3 : ℝ)) := by
          gcongr
        _ = B := by
          dsimp [B]
          rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hW.le]
          have hh : W ^ (1 / 6 : ℝ) * W ^ (1 / 3 : ℝ) = W ^ (1 / 2 : ℝ) := by rw [hpow]; norm_num
          field_simp
          rw [← hh]
          ring
  have hsmall : (2 * qG Y * log 2) ^ (-(2 / 3) : ℝ) *
      ((N / W) ^ (1 / 2 : ℝ) / (Y ^ (1 / 6 : ℝ) * D * log Y ^ (2 / 3 : ℝ))) ≤ S := by
    have hq : (2 * qG Y * log 2) ^ (-(2 / 3) : ℝ) ≤
        (2 * qG (2 * W) * log 2) ^ (-(2 / 3) : ℝ) := by
      apply rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
      gcongr
    have hid : (N / W) ^ (1 / 2 : ℝ) / (Y ^ (1 / 6 : ℝ) * D * log Y ^ (2 / 3 : ℝ)) =
        P / (W ^ (1 / 2 : ℝ) * Y ^ (1 / 6 : ℝ) * log Y ^ (2 / 3 : ℝ)) := by
      rw [(div_eq_iff hD0.ne').mp hroot]
      field_simp
    rw [hid]
    calc _ ≤ (2 * qG (2 * W) * log 2) ^ (-(2 / 3) : ℝ) *
        (P / (W ^ (1 / 2 : ℝ) * W ^ (1 / 6 : ℝ) * log W ^ (2 / 3 : ℝ))) := by
          gcongr
        _ = S := by dsimp [S]; rw [hpow]; norm_num
  have hthird : 0.69205 * (2 * qG Y * log 2) ^ (-(1 / 3) : ℝ) *
      ((N / W) ^ (1 / 2 : ℝ) * log D /
        (Y ^ (1 / 3 : ℝ) * D * log (log D) * log Y ^ (1 / 3 : ℝ))) ≤ T := by
    have hq : (2 * qG Y * log 2) ^ (-(1 / 3) : ℝ) ≤
        (2 * qG (2 * W) * log 2) ^ (-(1 / 3) : ℝ) := by
      apply rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
      gcongr
    have hid : (N / W) ^ (1 / 2 : ℝ) * log D /
        (Y ^ (1 / 3 : ℝ) * D * log (log D) * log Y ^ (1 / 3 : ℝ)) =
        P * log D / (W ^ (1 / 2 : ℝ) * Y ^ (1 / 3 : ℝ) * log (log D) * log Y ^ (1 / 3 : ℝ)) := by
      rw [(div_eq_iff hD0.ne').mp hroot]
      field_simp
    rw [hid]
    calc _ ≤ 0.69205 * (2 * qG (2 * W) * log 2) ^ (-(1 / 3) : ℝ) *
        (P * (log N / 2) / (W ^ (1 / 2 : ℝ) * W ^ (1 / 3 : ℝ) * log (log D) * log W ^ (1 / 3 : ℝ))) := by
          gcongr
        _ = T := by
          dsimp [T]
          rw [hpow]
          norm_num only [show (1 / 2 : ℝ) + 1 / 3 = 5 / 6 by norm_num]
          rw [show P * (log N / 2) = log N ^ (A + 2) / 2 by rw [← hPnext]; ring]
          ring
  have hmiddle : (√(N / W) + √Y) / (D * log 2) ≤
      P * (W ^ (-(1 / 2) : ℝ) + (2 * W / N) ^ (1 / 2 : ℝ)) / log 2 := by
    have hid : (√(N / W) + √Y) / (D * log 2) =
        P / log 2 * (1 / √W + √(Y / N)) := by
      dsimp [D]
      rw [sqrt_div hN0.le, sqrt_div hY.le]
      field_simp
    rw [hid]
    calc _ ≤ P / log 2 * (1 / √W + √(2 * W / N)) := by gcongr
        _ = _ := by rw [rpow_neg hW.le, ← sqrt_eq_rpow, ← sqrt_eq_rpow]; ring
  have hsmallCoeff : Decomp148a.smallCoeff (N / W) Y D ≤ 2 * Mphi0 W * Mphi D * (B + S + T) := by
    unfold Decomp148a.smallCoeff
    apply mul_le_mul
    · gcongr
    · exact add_le_add (add_le_add hbal hsmall) hthird
    · unfold Decomp148a.balance
      positivity
    · positivity
  have hlargeCoeff : Decomp148a.largeCoeff (N / W) Y D ≤ 2 * Mphi D *
      (2 / log 2 + B + P * (W ^ (-(1 / 2) : ℝ) + (2 * W / N) ^ (1 / 2 : ℝ)) / log 2) := by
    unfold Decomp148a.largeCoeff
    gcongr
  have hid : mbarJ N A W = 2 * Mphi0 W * Mphi D * (B + S + T) +
      2 * Mphi D * (2 / log 2 + B + P * (W ^ (-(1 / 2) : ℝ) + (2 * W / N) ^ (1 / 2 : ℝ)) / log 2) := by
    unfold mbarJ
    rw [← hlogD]
    dsimp [B, S, T, D, P]
    ring
  rw [hid]
  exact add_le_add hsmallCoeff hlargeCoeff

/-- Assemble the exact slice scale statement from the smaller coefficient leaf.
Journal display 31 on p. 1240. Only rectangle_coefficient_bound remains OPEN. -/
theorem slice_scale_assembly (α A u X₂ ε₁ : ℝ) (n j : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hj : j ∈ slices n ε₁) :
    let X := (n : ℝ) / w n ε₁ j
    let Y := min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)
    let D := √(n : ℝ) / log n ^ (A + 1)
    Decomp148a.mJ X Y D * Decomp148a.scale X Y D ≤
      (mbarJ n A (U7153.zz n) * n * √(1 + ε₁) / log n ^ (A - 1)) / 4 := by
  let W := w n ε₁ j
  let Y := min (U7153.yy n) ((1 + ε₁) * W)
  let D := √(n : ℝ) / log n ^ (A + 1)
  have hN := hX.trans hn
  have hN1 : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hN
  have hn0 : (0 : ℝ) < n := by linarith
  have hnN : 0 < n := by exact_mod_cast hn0
  have hL := Lemma11C164.log_lower n hN
  have hL0 : 0 < log (n : ℝ) := by linarith
  have hw : 0 < W := w_pos n j ε₁ hnN hε
  have hr := SliceRemainder236.slice_bilinear_basic_ranges n j ε₁ hN hε hε1 hj
  have hY : 0 < Y := by change 0 < min _ _; linarith [hr.2.1]
  have hzw : U7153.zz n ≤ W := by
    dsimp [W, w]
    exact le_mul_of_one_le_right (rpow_nonneg hn0.le _)
      (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + ε₁))
  have hz : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
  have hlz : 2750 ≤ log (U7153.zz n) := by
    rw [U7153.zz, log_rpow hn0]
    linarith
  have hlw : 2750 ≤ log W := hlz.trans (log_le_log hz hzw)
  have hd := SliceRemainder236.slice_Dstar_ge α A u X₂ n hα hα1 hA hc hX hn
  have hm := (rectangle_coefficient_bound n W Y A hN1 hw hlw hr.2.2.2.1.le
    hr.2.2.2.2 hA (by linarith) hd).trans
      (MbarCompare339.mbar_antitone n A (U7153.zz n) W hN1 hz hlz hzw
        (SliceRemainder236.slice_w_le_sqrt_half n j ε₁ hN hε hj) hd)
  have hs := Scale339.scale_bound n W Y A ε₁ hN1 hw hY.le hε (min_le_right _ _)
    hA.le (by linarith) (by linarith [hd])
  have hm0 := MbarCompare339.mbar_nonneg n A (U7153.zz n) hN1 hz hlz hd
  have hs0 : 0 ≤ Decomp148a.scale ((n : ℝ) / W) Y D := by
    unfold Decomp148a.scale
    dsimp [D]
    positivity
  change Decomp148a.mJ ((n : ℝ) / W) Y D * Decomp148a.scale ((n : ℝ) / W) Y D ≤ _
  calc _ ≤ mbarJ n A (U7153.zz n) * (n * √(1 + ε₁) / (4 * log n ^ (A - 1))) :=
          mul_le_mul hm hs hs0 hm0
       _ = _ := by ring

end
end LeanLab.BS2022GRH.Decomp339c
#print axioms LeanLab.BS2022GRH.Decomp339c.rectangle_coefficient_bound
#print axioms LeanLab.BS2022GRH.Decomp339c.slice_scale_assembly

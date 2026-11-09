/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Elementary parts of the Lemma 8 slice cutoff guards, journal p. 1239.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Correction339

namespace LeanLab.BS2022GRH.Cutoff339
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The explicit qG coefficient is at least its constant term on the Lemma 8 domain.
Journal p. 1216 Lemma 3, used in the cutoff guard on p. 1239. -/
theorem qG_lower (Y : ℝ) (hY : 25 ≤ Y) : 0.165 ≤ qG Y := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hl : 1 ≤ log Y := by
    rw [le_log_iff_exp_le hY0]
    linarith [exp_one_lt_d9]
  have hll : 0 ≤ log (log Y) := log_nonneg hl
  have h4 : 0 < Y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hY0 _
  have hs : Y ^ (1 / 4 : ℝ) ≤ √Y := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have hneg : 237.934 / (√Y * log Y) ≤ 939.260 / (Y ^ (1 / 4 : ℝ) * log Y) := by
    apply div_le_div₀ (by norm_num) (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_right hs (by linarith)
  have hrest : 0 ≤ 12.683 / log Y + 254.980 / log Y ^ 2 + 2607.854 / log Y ^ 3 +
      11605.056 / log Y ^ 4 + 1.314 * log Y / Y ^ (1 / 4 : ℝ) +
      0.092 * log (log Y) / Y ^ (1 / 4 : ℝ) + 60.883 / Y ^ (1 / 4 : ℝ) +
      8.250 * log (log Y) / (Y ^ (1 / 4 : ℝ) * log Y) := by positivity
  unfold qG
  linarith

/-- The upper square root guard follows just from w at least 25 and Y at most twice w.
This discharges one cutoff condition on journal p. 1239 independently of A. -/
theorem cutoff_le_sqrt (Y w : ℝ) (hw : 25 ≤ w) (hwY : w ≤ Y) (hYw : Y ≤ 2 * w) :
    Decomp148a.cutoff Y ≤ √w := by
  have hY : 25 ≤ Y := hw.trans hwY
  have hY0 : 0 < Y := by linarith
  have hw0 : 0 < w := by linarith
  have hl : 1 ≤ log Y := by
    rw [le_log_iff_exp_le hY0]
    linarith [exp_one_lt_d9]
  have hq := qG_lower Y hY
  have hden : (1 / 5 : ℝ) ≤ 2 * log 2 * qG Y * log Y := by
    have h2 : (0.69 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
    have hmul := mul_le_mul (mul_le_mul_of_nonneg_left
      (mul_le_mul h2 hq (by norm_num) (by positivity)) (by norm_num : (0 : ℝ) ≤ 2))
      hl (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 2 * (log 2 * qG Y))
    norm_num at hmul
    linarith
  have hden0 : 0 < 2 * log 2 * qG Y * log Y := by linarith
  have hc0 : 0 ≤ Decomp148a.cutoff Y := rpow_nonneg (by positivity) _
  have hc3 : Decomp148a.cutoff Y ^ (3 : ℕ) = √Y / (2 * log 2 * qG Y * log Y) := by
    unfold Decomp148a.cutoff
    rw [← rpow_natCast, ← rpow_mul (by positivity : 0 ≤ √Y / (2 * log 2 * qG Y * log Y))]
    norm_num
  have hs : √Y ≤ 2 * √w := by
    calc √Y ≤ √(4 * w) := sqrt_le_sqrt (by linarith)
      _ = _ := by rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  apply (pow_le_pow_iff_left₀ hc0 (sqrt_nonneg w) (by norm_num : (3 : ℕ) ≠ 0)).mp
  calc
    _ = √Y / (2 * log 2 * qG Y * log Y) := hc3
    _ ≤ 5 * √Y := by apply (div_le_iff₀ hden0).mpr; nlinarith [sqrt_nonneg Y]
    _ ≤ 10 * √w := by linarith
    _ ≤ w * √w := mul_le_mul_of_nonneg_right (by linarith) (sqrt_nonneg _)
    _ = _ := by rw [pow_succ, sq_sqrt hw0.le]

/-- D star is strictly below the rectangular square root on the slice domain.
The strict prime endpoint Y greater than w supplies strictness, journal p. 1239. -/
theorem Dstar_lt_rectangle (n j : ℕ) (A ε₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1)
    (hA : 0 < A) (hj : j ∈ slices n ε₁) :
    √(n : ℝ) / log n ^ (A + 1) <
      √(((n : ℝ) / w n ε₁ j) * min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hnN : 0 < n := by exact_mod_cast hn0
  have hw := w_pos n j ε₁ hnN hε
  have hr := SliceRemainder236.slice_bilinear_basic_ranges n j ε₁ hn hε hε1 hj
  have hquot : 0 < (n : ℝ) / w n ε₁ j := div_pos hn0 hw
  have hprod : (n : ℝ) < ((n : ℝ) / w n ε₁ j) *
      min (U7153.yy n) ((1 + ε₁) * w n ε₁ j) := by
    have hh := mul_lt_mul_of_pos_left hr.2.2.2.1 hquot
    simpa only [div_mul_cancel₀ _ hw.ne'] using hh
  exact (Correction339.Dstar_le_sqrt n A
    (by linarith [Lemma11C164.log_lower n hn]) hA).trans_lt (sqrt_lt_sqrt hn0.le hprod)

/-- The cube root cutoff is below D star using only the second condition of display 25.
The square root w guard and alpha below one sixteenth give the exponent comparison.
Journal p. 1239, the other upper cutoff condition of Lemma 8. -/
theorem cutoff_le_Dstar (α A u X₂ ε₁ : ℝ) (n j : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hj : j ∈ slices n ε₁) :
    Decomp148a.cutoff (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) ≤
      √(n : ℝ) / log n ^ (A + 1) := by
  have hN := hX.trans hn
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hN
  have hnN : 0 < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n :=
    (one_lt_exp_iff.mpr (exp_pos 10)).le.trans hN
  have hX1 : 1 < X₂ := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX
  have hL := Lemma11C164.log_lower n hN
  have hL0 : 0 < log (n : ℝ) := by linarith
  have hP : 0 < log (n : ℝ) ^ (A + 1) := rpow_pos_of_pos hL0 _
  have hc19 : Cond19 α A u X₂ :=
    ⟨(le_max_left _ _).trans hc.1, hc.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
  have h19 := DecompC169b.cond19_at α A u X₂ n hα hA hc19 hX1 hn
  have hratio : 1 ≤ (n : ℝ) ^ α / log n ^ (A + 1) :=
    (one_le_exp_iff.mpr (by linarith [hc.2.2.2.1] : 0 ≤ u)).trans h19
  have hden : log (n : ℝ) ^ (A + 1) ≤ (n : ℝ) ^ α := by
    simpa only [one_mul] using (le_div_iff₀ hP).mp hratio
  have hr := SliceRemainder236.slice_bilinear_basic_ranges n j ε₁ hN hε hε1 hj
  calc
    _ ≤ √(w n ε₁ j) := cutoff_le_sqrt _ _ hr.2.2.1 hr.2.2.2.1.le hr.2.2.2.2
    _ ≤ √(U7153.yy n) := sqrt_le_sqrt (w_lt_y hnN hε hj).le
    _ = (n : ℝ) ^ (1 / 6 : ℝ) := by
      rw [sqrt_eq_rpow, U7153.yy, ← rpow_mul hn0.le]
      norm_num
    _ ≤ (n : ℝ) ^ ((1 / 2 : ℝ) - α) :=
      rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ = √(n : ℝ) / (n : ℝ) ^ α := by rw [rpow_sub hn0, sqrt_eq_rpow]
    _ ≤ _ := div_le_div_of_nonneg_left (sqrt_nonneg _) hP hden

end
end LeanLab.BS2022GRH.Cutoff339
#print axioms LeanLab.BS2022GRH.Cutoff339.qG_lower
#print axioms LeanLab.BS2022GRH.Cutoff339.cutoff_le_sqrt
#print axioms LeanLab.BS2022GRH.Cutoff339.Dstar_lt_rectangle

#print axioms LeanLab.BS2022GRH.Cutoff339.cutoff_le_Dstar

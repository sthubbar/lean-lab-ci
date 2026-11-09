/- AI wrote this Lean code for CODEX task339. Goldbach is open.
The balancing guard for the slice substitution in Lemma 8.
Journal p. 1239 and display 25 on pp. 1234 and 1235.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Scalar339

namespace LeanLab.BS2022GRH.Balance339
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The logarithmic ratio required for the balancing guard decreases past two.
Auxiliary logarithm comparison for the proof on journal p. 1239. -/
theorem log_affine_half_antitone :
    AntitoneOn (fun t : ℝ => log (t + log 2) - t / 2) (Set.Ici 2) := by
  intro a ha b hb hab
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have ha2 : 2 ≤ a := ha
  have ha0 : 0 < a + log 2 := by linarith
  have hb0 : 0 < b + log 2 := by linarith
  have hlog := log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [log_div hb0.ne' ha0.ne',
    show (b + log 2) / (a + log 2) - 1 = (b - a) / (a + log 2) by field_simp <;> ring] at hlog
  have hdiv : (b - a) / (a + log 2) ≤ (b - a) / 2 :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hab) (by norm_num) (by linarith)
  dsimp
  nlinarith only [hlog, hdiv]

/-- Display 25 and qG at most 0.17 imply the balancing inequality in logarithms.
Here L is log N, u is log w and v is log Y. Journal p. 1239. -/
theorem logarithmic_balance (L u v q A : ℝ) (hL : 22000 ≤ L)
    (hu : L / 8 ≤ u) (hv : u ≤ v) (hv1 : v ≤ u + log 2)
    (hq0 : 0 < q) (hq : q ≤ 0.17)
    (hthird : 0.44 ≤ exp (L / 48) / L ^ (A + 4 / 3)) :
    (v - u) / 2 + (A + 1) * log L ≤ (v / 2 - log (2 * log 2 * q * v)) / 3 := by
  have hL0 : 0 < L := by linarith
  have hu2 : 2 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2u : log (2 : ℝ) ≤ 0.7 := by linarith [log_two_lt_d9]
  have ht := log_le_log (by norm_num : (0 : ℝ) < 0.44) hthird
  rw [log_div (exp_ne_zero _) (rpow_pos_of_pos hL0 _).ne', log_exp, log_rpow hL0] at ht
  have hmono := log_affine_half_antitone (by change 2 ≤ L / 8; linarith : L / 8 ∈ Set.Ici 2)
    hu2 hu
  have hC : 2 * log 2 * q * v ≤ (0.34 * log 2) * (u + log 2) := by
    calc
      _ ≤ 2 * log 2 * 0.17 * (u + log 2) := by gcongr
      _ = _ := by ring
  have hClog := log_le_log (by positivity : 0 < 2 * log 2 * q * v) hC
  rw [log_mul (by positivity : (0.34 : ℝ) * log 2 ≠ 0)
    (by linarith : u + log 2 ≠ 0)] at hClog
  have hnum : (0.68 * log 2) * (L / 8 + log 2) ≤ (0.44 : ℝ) ^ (3 : ℕ) * L := by
    have hh : (0.68 * log 2) * (L / 8 + log 2) ≤ (0.68 * 0.7) * (L / 8 + 0.7) := by
      gcongr
    nlinarith only [hh, hL]
  have hnlog := log_le_log (by positivity : 0 < (0.68 * log 2) * (L / 8 + log 2)) hnum
  rw [log_mul (by positivity : (0.68 : ℝ) * log 2 ≠ 0)
    (by linarith : L / 8 + log 2 ≠ 0),
    log_mul (by norm_num : (0.44 : ℝ) ^ (3 : ℕ) ≠ 0) hL0.ne', log_pow] at hnlog
  have heq : log (0.68 * log 2) = log 2 + log (0.34 * log 2) := by
    rw [show (0.68 : ℝ) * log 2 = 2 * (0.34 * log 2) by ring,
      log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (0.34 : ℝ) * log 2 ≠ 0)]
  dsimp at hmono
  rw [heq] at hnlog
  norm_num only [Nat.cast_ofNat] at hnlog
  nlinarith only [ht, hmono, hClog, hnlog, hv1]

/-- The full balancing guard for every indexed slice follows from display 25.
Journal p. 1239 application of Lemma 8. The upper cutoff guards are separate. -/
theorem slice_balancing (α A u X₂ ε₁ : ℝ) (n j : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hj : j ∈ slices n ε₁) :
    √(((n : ℝ) / w n ε₁ j) * min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) /
      (√(n : ℝ) / log n ^ (A + 1)) ≤
        Decomp148a.cutoff (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) := by
  let W := w n ε₁ j
  let Y := min (U7153.yy n) ((1 + ε₁) * W)
  let D := √(n : ℝ) / log n ^ (A + 1)
  have hN := hX.trans hn
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hN
  have hnN : 0 < n := by exact_mod_cast hn0
  have hL := Lemma11C164.log_lower n hN
  have hL0 : 0 < log (n : ℝ) := by linarith
  have hw0 : 0 < W := w_pos n j ε₁ hnN hε
  have hr := SliceRemainder236.slice_bilinear_basic_ranges n j ε₁ hN hε hε1 hj
  have hY0 : 0 < Y := by change 0 < min _ _; linarith [hr.2.1]
  have hY1 : 1 < Y := by change 1 < min _ _; linarith [hr.2.1]
  have hlogY : 0 < log Y := log_pos hY1
  have hzw : U7153.zz n ≤ W := by
    dsimp [W, w]
    exact le_mul_of_one_le_right (rpow_nonneg hn0.le _)
      (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + ε₁))
  have hu : log (n : ℝ) / 8 ≤ log W := by
    have hh := log_le_log (rpow_pos_of_pos hn0 (1 / 8 : ℝ)) hzw
    rw [log_rpow hn0] at hh
    linarith
  have hv : log W ≤ log Y := log_le_log hw0 hr.2.2.2.1.le
  have hv1 : log Y ≤ log W + log 2 := by
    have hh := log_le_log hY0 hr.2.2.2.2
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hw0.ne'] at hh
    linarith
  have hq0 := DecompC164b.qG_positive Y hr.2.1
  have hq := Scalar339.qG_upper Y hY0 (by linarith : 2750 ≤ log Y)
  have ht := Scalar339.third_condition_at α A u X₂ n hA hc
    ((one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX) hn
  have ht' : 0.44 ≤ exp (log (n : ℝ) / 48) / log n ^ (A + 4 / 3) := by
    convert ht using 1
    rw [rpow_def_of_pos hn0]
    congr 2
    ring
  have hb := logarithmic_balance (log n) (log W) (log Y) (qG Y) A hL hu hv hv1 hq0 hq ht'
  have hx0 : 0 < (n : ℝ) / W := div_pos hn0 hw0
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hd0 : 0 < 2 * log 2 * qG Y * log Y := by positivity
  have hquot : 0 < √Y / (2 * log 2 * qG Y * log Y) := by positivity
  have hcut0 : 0 < Decomp148a.cutoff Y := rpow_pos_of_pos hquot _
  have hlogD : log D = log n / 2 - (A + 1) * log (log n) := by
    dsimp [D]
    rw [log_div (sqrt_pos.mpr hn0).ne' (rpow_pos_of_pos hL0 _).ne',
      log_sqrt hn0.le, log_rpow hL0]
  have hlogX : log ((n : ℝ) / W) = log n - log W := log_div hn0.ne' hw0.ne'
  have hlogB : log (√(((n : ℝ) / W) * Y) / D) =
      (log Y - log W) / 2 + (A + 1) * log (log n) := by
    rw [log_div (sqrt_pos.mpr (mul_pos hx0 hY0)).ne' hD0.ne',
      log_sqrt (mul_pos hx0 hY0).le, log_mul hx0.ne' hY0.ne', hlogX, hlogD]
    ring
  have hlogC : log (Decomp148a.cutoff Y) =
      (log Y / 2 - log (2 * log 2 * qG Y * log Y)) / 3 := by
    unfold Decomp148a.cutoff
    rw [log_rpow hquot, log_div (sqrt_pos.mpr hY0).ne' hd0.ne', log_sqrt hY0.le]
    ring
  change √(((n : ℝ) / W) * Y) / D ≤ Decomp148a.cutoff Y
  apply (log_le_log_iff (div_pos (sqrt_pos.mpr (mul_pos hx0 hY0)) hD0) hcut0).mp
  rw [hlogB, hlogC]
  exact hb

end
end LeanLab.BS2022GRH.Balance339
#print axioms LeanLab.BS2022GRH.Balance339.log_affine_half_antitone
#print axioms LeanLab.BS2022GRH.Balance339.logarithmic_balance

#print axioms LeanLab.BS2022GRH.Balance339.slice_balancing

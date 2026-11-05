/-
BHP1997, pages 3 and 51. Audit of a fixed-log density convention.
These theorems concern the explicit reciprocal-log integral only.
They do not refute the paper or either existential weight leaf.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Task308
open MeasureTheory Set

/-- Page 51 normalization audit. Replacing the reciprocal-log density on a dyadic
interval by its left-endpoint value incurs at least a log-squared error. -/
theorem reciprocal_log_center_gap {Y : ℝ} (hY : 2 ≤ Y) :
    Y / (12 * (Real.log Y)^2) ≤
      Y / Real.log Y - ∫ t in Y..(2 * Y), 1 / Real.log t := by
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 < Y := by linarith
  let L := Real.log Y
  have hL : 0 < L := Real.log_pos hY1
  let g : ℝ → ℝ := fun t => 1 / L - 1 / Real.log t
  have hab : Y ≤ 2 * Y := by linarith
  have hm1 : Y ≤ 3 * Y / 2 := by linarith
  have hm2 : 3 * Y / 2 ≤ 2 * Y := by linarith
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Icc Y (2 * Y)) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact (continuousAt_const.div
      (Real.continuousAt_log (by linarith : t ≠ 0)) (ne_of_gt (Real.log_pos ht1))).continuousWithinAt
  have hcg : ContinuousOn g (Icc Y (2 * Y)) := continuousOn_const.sub hc
  have hi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume Y (2 * Y) :=
    hc.intervalIntegrable_of_Icc hab
  have hleft : IntervalIntegrable g volume Y (3 * Y / 2) :=
    (hcg.mono (Icc_subset_Icc le_rfl hm2)).intervalIntegrable_of_Icc hm1
  have hright : IntervalIntegrable g volume (3 * Y / 2) (2 * Y) :=
    (hcg.mono (Icc_subset_Icc hm1 le_rfl)).intervalIntegrable_of_Icc hm2
  have hg0 : ∀ t ∈ Icc Y (2 * Y), 0 ≤ g t := by
    intro t ht
    have hl : L ≤ Real.log t := Real.log_le_log hY0 ht.1
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hL hl)
  have hleft0 : 0 ≤ ∫ t in Y..(3 * Y / 2), g t := by
    apply intervalIntegral.integral_nonneg hm1
    intro t ht
    exact hg0 t ⟨ht.1, ht.2.trans hm2⟩
  have hgap : ∀ t ∈ Icc (3 * Y / 2) (2 * Y), 1 / (6 * L^2) ≤ g t := by
    intro t ht
    have htY : Y ≤ t := hm1.trans ht.1
    have ht1 : 1 < t := hY1.trans_le htY
    have hlt : 0 < Real.log t := Real.log_pos ht1
    have hhalf : (1/3 : ℝ) ≤ Real.log (3/2) := by
      have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3/2 by norm_num)
      norm_num at hh ⊢
      exact hh
    have hlow : Real.log (3/2) + L ≤ Real.log t := by
      have hh := Real.log_le_log (show (0 : ℝ) < (3/2)*Y by positivity)
        (show (3/2)*Y ≤ t by linarith [ht.1])
      rw [Real.log_mul (by norm_num) hY0.ne'] at hh
      exact hh
    have hhigh : Real.log t ≤ 2 * L := by
      have hh := Real.log_le_log (show 0 < t by linarith) ht.2
      rw [Real.log_mul (by norm_num) hY0.ne'] at hh
      have h2 := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hY
      change Real.log 2 ≤ L at h2
      linarith
    have hdiff : 1 / L - 1 / Real.log t =
        (Real.log t - L) / (L * Real.log t) := by
      field_simp
      <;> ring
    change 1 / (6 * L^2) ≤ 1 / L - 1 / Real.log t
    rw [hdiff]
    apply (div_le_div_iff₀ (by positivity : 0 < 6 * L^2) (mul_pos hL hlt)).2
    have ha := mul_le_mul_of_nonneg_left hhigh hL.le
    have hb := mul_le_mul_of_nonneg_left
      (show (1/3 : ℝ) ≤ Real.log t - L by linarith) (show 0 ≤ 6 * L^2 by positivity)
    nlinarith only [ha, hb]
  have hrightBound := intervalIntegral.integral_mono_on hm2
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / (6 * L^2)) volume _ _)
    hright hgap
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hrightBound
  have hconst : (2 * Y - 3 * Y / 2) * (1 / (6 * L^2)) = Y / (12 * L^2) := by ring
  rw [hconst] at hrightBound
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have heq : (∫ t in Y..(2 * Y), g t) =
      Y / L - ∫ t in Y..(2 * Y), 1 / Real.log t := by
    dsimp only [g]
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  change Y / (12 * L^2) ≤ Y / L - ∫ t in Y..(2 * Y), 1 / Real.log t
  linarith only [hleft0, hrightBound, hsplit, heq]

/-- Page 51 normalization audit. The reciprocal-log integral cannot be centered
at Y divided by log Y with a uniform cubic-log saving.
This is an explicit ideal-density countermodel, not a claim about the paper weights. -/
theorem reciprocal_log_not_cubic_center :
    ¬ ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y →
      |(∫ t in Y..(2 * Y), 1 / Real.log t) - Y / Real.log Y| ≤
        C * Y / (Real.log Y)^3 := by
  rintro ⟨C, hC⟩
  let L := max (Real.log 2) (12 * C + 1)
  let Y := Real.exp L
  have hY : 2 ≤ Y := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (le_max_left _ _)
  have hY0 : 0 < Y := Real.exp_pos L
  have hL : 0 < L := (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).trans_le (le_max_left _ _)
  have hLY : Real.log Y = L := Real.log_exp L
  have habs : Y / Real.log Y - (∫ t in Y..(2 * Y), 1 / Real.log t) ≤
      |(∫ t in Y..(2 * Y), 1 / Real.log t) - Y / Real.log Y| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have hh := (reciprocal_log_center_gap hY).trans (habs.trans (hC Y hY))
  rw [hLY] at hh
  have hc := (div_le_div_iff₀ (by positivity : 0 < 12 * L^2) (by positivity : 0 < L^3)).mp hh
  have hm : (Y * L^2) * L ≤ (Y * L^2) * (12 * C) := by nlinarith only [hc]
  have hle : L ≤ 12 * C :=
    (mul_le_mul_iff_right₀ (mul_pos hY0 (sq_pos_of_pos hL))).mp hm
  have hlarge : 12 * C + 1 ≤ L := le_max_right _ _
  linarith

end LeanLab.BHP1997.Task308

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open intervalIntegral Real

noncomputable section

def chord (l h t : ℝ) : ℝ := (l + h - t) / (l * h)

theorem one_div_le_chord {l h t : ℝ} (hl : 0 < l) (hlt : l ≤ t) (hth : t ≤ h) :
    1 / t ≤ chord l h t := by
  have ht : 0 < t := hl.trans_le hlt
  have hh : 0 < h := ht.trans_le hth
  have hlh : 0 < l * h := mul_pos hl hh
  have hz : (0 : ℝ) ≤ (t - l) * (h - t) := mul_nonneg (sub_nonneg.mpr hlt) (sub_nonneg.mpr hth)
  rw [chord]
  field_simp
  nlinarith

theorem chord_integral {l h : ℝ} (hl : 0 < l) (hll : l ≤ h) :
    (∫ t in l..h, chord l h t) = (h - l) ^ 2 / (2 * l * h) := by
  have hh : 0 < h := hl.trans_le hll
  have hlin : IntervalIntegrable (chord l h) volume l h := continuousOn.intervalIntegrable
  rw [intervalIntegral.integral_add intervalIntegrable_const hlin]
  rw [intervalIntegral.integral_sub intervalIntegrable_const hlin]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_id]
  simp [chord]
  field_simp
  ring

theorem chord_sq_integral {l h : ℝ} (hl : 0 < l) (hll : l ≤ h) :
    (∫ t in l..h, (chord l h t) ^ 2) = (h - l) * (h * h + h * l + l * l) / (3 * l * h * l * h) := by
  have hh : 0 < h := hl.trans_le hll
  have hlin : IntervalIntegrable (fun t => (chord l h t) ^ 2) volume l h :=
    (continuousOn.intervalIntegrable continuousOn_const).pow 2
  rw [intervalIntegral.integral_add intervalIntegrable_const hlin]
  rw [intervalIntegral.integral_sub intervalIntegrable_const hlin]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_id]
  simp [chord]
  field_simp
  ring

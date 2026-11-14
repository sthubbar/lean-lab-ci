/-
Jia 1996 pages 283 to 285, displays 60 and 64.
Source https://doi.org/10.4064/aa-77-3-207-287.
The inner reciprocal integrals reduce to logarithms and squared logarithms.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Languasco2004.Integral565
open Real intervalIntegral
noncomputable section

/-- Pages 283 to 285: integrate the logarithm produced by the innermost reciprocal integral. -/
theorem integral_log_ratio (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, log (u / a) / u) = log (b / a)^2 / 2 := by
  have hd : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun v : ℝ => log (v / a)^2 / 2) (log (u / a) / u) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 < u := ha.trans_le hu.1
    have h := (((hasDerivAt_id u).div_const a).log (div_ne_zero hu0.ne' ha.ne')).pow 2
    have h' := h.div_const 2
    simp only [Pi.pow_apply, id_eq] at h'
    convert h' using 1 <;> field_simp <;> ring
  have hi : IntervalIntegrable (fun u => log (u / a) / u) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · fun_prop
      · intro u hu
        exact div_ne_zero (ne_of_gt (ha.trans_le hu.1)) ha.ne'
    · fun_prop
    · intro u hu
      exact ne_of_gt (ha.trans_le hu.1)
  have h := integral_eq_sub_of_hasDerivAt hd hi
  simpa only [div_self ha.ne', log_one, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_div, sub_zero] using h

/-- Pages 283 to 285: the two inner reciprocal integrals give half a squared logarithm. -/
theorem double_reciprocal (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, (1 / u) * ∫ v in a..u, 1 / v) = log (b / a)^2 / 2 := by
  have he : (∫ u in a..b, (1 / u) * ∫ v in a..u, 1 / v) =
      ∫ u in a..b, log (u / a) / u := by
    apply integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 < u := ha.trans_le hu.1
    dsimp only
    rw [integral_one_div_of_pos ha hu0]
    ring
  rw [he]
  exact integral_log_ratio a b ha hab

/-- Pages 284 and 285: subtracting two inner triangular domains gives the printed band integral. -/
theorem double_reciprocal_band (a l h : ℝ) (ha : 0 < a) (hal : a ≤ l) (hlh : l ≤ h) :
    (∫ u in l..h, (1 / u) * ∫ v in a..u, 1 / v) =
      (log (h / a)^2 - log (l / a)^2) / 2 := by
  have hd : ∀ u ∈ Set.uIcc l h,
      HasDerivAt (fun v : ℝ => log (v / a)^2 / 2) (log (u / a) / u) u := by
    intro u hu
    rw [Set.uIcc_of_le hlh] at hu
    have hu0 : 0 < u := ha.trans_le (hal.trans hu.1)
    have h' := ((((hasDerivAt_id u).div_const a).log
      (div_ne_zero hu0.ne' ha.ne')).pow 2).div_const 2
    simp only [Pi.pow_apply, id_eq] at h'
    convert h' using 1 <;> field_simp <;> ring
  have hi : IntervalIntegrable (fun u => log (u / a) / u) MeasureTheory.volume l h := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlh
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · fun_prop
      · intro u hu
        exact div_ne_zero (ne_of_gt (ha.trans_le (hal.trans hu.1))) ha.ne'
    · fun_prop
    · intro u hu
      exact ne_of_gt (ha.trans_le (hal.trans hu.1))
  have he : (∫ u in l..h, (1 / u) * ∫ v in a..u, 1 / v) =
      ∫ u in l..h, log (u / a) / u := by
    apply integral_congr
    intro u hu
    rw [Set.uIcc_of_le hlh] at hu
    dsimp only
    rw [integral_one_div_of_pos ha (ha.trans_le (hal.trans hu.1))]
    ring
  rw [he, integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- Pages 283 to 285: a nonzero interval gives a nonzero inner reciprocal model. -/
theorem reciprocal_instance :
    (∫ u in (1 : ℝ)..2, (1 / u) * ∫ v in (1 : ℝ)..u, 1 / v) = log 2 ^ 2 / 2 ∧
      0 < log 2 ^ 2 / 2 := by
  constructor
  · simpa using double_reciprocal 1 2 (by norm_num) (by norm_num)
  · exact div_pos (sq_pos_of_pos (log_pos (by norm_num))) (by norm_num)

#print axioms integral_log_ratio
#print axioms double_reciprocal
#print axioms double_reciprocal_band
#print axioms reciprocal_instance
end
end LeanLab.Languasco2004.Integral565

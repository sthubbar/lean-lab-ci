/-
The geometric integral in the sketch of Theorem 6.2, P0029 page 22.
This computes the displayed integral with its logarithmic prefactor.
It does not refute Theorem 6.2. The sketch needs an additional estimate.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- Page 22 after sigma equals one minus lambda.
The logarithmic prefactor cancels the decay of the geometric integral. -/
theorem density_integral_exact150 {d X : ℝ} (hd : 0 < d) (hX : 1 < X) :
    Real.log X * (∫ t in (0 : ℝ)..(1 / 2), X ^ (-d * t)) =
      (1 - X ^ (-d / 2)) / d := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hc : -d * Real.log X ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hd.ne') hlog.ne'
  have hpow (t : ℝ) : X ^ (-d * t) = Real.exp ((-d * Real.log X) * t) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < X)]
    congr 1
    ring
  simp_rw [hpow]
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  rw [Real.rpow_def_of_pos (by linarith : 0 < X)]
  rw [show Real.log X * (-d / 2) = (-d * Real.log X) * (1 / 2) by ring]
  field_simp
  <;> ring

/-- Page 22, the geometric integral times log X tends to one over d, not zero. -/
theorem density_integral_limit150 {d : ℝ} (hd : 0 < d) :
    Tendsto (fun X : ℝ => Real.log X * (∫ t in (0 : ℝ)..(1 / 2), X ^ (-d * t)))
      atTop (𝓝 (1 / d)) := by
  have hpow := tendsto_rpow_neg_atTop (show 0 < d / 2 by linarith)
  have hlim : Tendsto (fun X : ℝ => (1 - X ^ (-(d / 2))) / d) atTop (𝓝 (1 / d)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      atTop (𝓝 1)).sub hpow).div_const d
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  rw [density_integral_exact150 hd hX]
  congr 3
  ring

/-- Page 22, shrinking the geometric integral alone does not remove its log prefactor. -/
theorem density_integral_not_zero150 {d : ℝ} (hd : 0 < d) :
    ¬ Tendsto (fun X : ℝ => Real.log X * (∫ t in (0 : ℝ)..(1 / 2), X ^ (-d * t)))
      atTop (𝓝 0) := by
  intro h
  exact (one_div_pos.mpr hd).ne' (tendsto_nhds_unique (density_integral_limit150 hd) h)

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.density_integral_exact150
#print axioms LeanLab.BhowmikGrimmelt2026.density_integral_limit150
#print axioms LeanLab.BhowmikGrimmelt2026.density_integral_not_zero150

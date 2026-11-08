import LeanLab.HelfgottMajor.Numerator457
import LeanLab.HelfgottMajor.LogWeight457

/-!
Absolute convergence and qualitative decay of the principal contour.
Source P0014 pages 34 and 35, displays 4.13 to 4.15.
The sharp numerical energy budget and the prime sum contour identity remain separate inputs.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Convergence457
open Real MeasureTheory Filter Contour457
open scoped Topology

/-- The actual principal contour integrand is absolutely integrable for every positive x.
Source P0014 pages 34 and 35, the Cauchy Schwarz justification for display 4.13.
-/
theorem principal_contour_integrable (δ x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
  have hL := LogWeight457.principal_log_weight_memLp_two
  have hG := (Numerator457.gaussian_numerator_L2 δ).1
  have hi : Integrable (fun t : ℝ => ‖principalLogWeight t‖ * ‖gaussianNumerator δ t‖ / sqrt x) :=
    (hL.norm.integrable_mul hG.norm).div_const _
  have hc : Continuous (fun t : ℝ => (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) :=
    (continuous_const_cpow' (by exact_mod_cast hx.ne')).comp (by fun_prop)
  have hmeas := (hL.aestronglyMeasurable.mul hG.aestronglyMeasurable).mul hc.aestronglyMeasurable
  have hfact : Integrable (fun t : ℝ => principalLogWeight t * gaussianNumerator δ t *
      (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) := by
    apply hi.mono' hmeas
    filter_upwards [] with t
    have hpow : ‖(x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)‖ = (sqrt x)⁻¹ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
        Complex.I_im, zero_mul, sub_zero, add_zero]
      rw [rpow_neg hx.le, sqrt_eq_rpow]
    simp only [Pi.mul_apply]
    rw [norm_mul, norm_mul, hpow, div_eq_mul_inv]
  apply hfact.congr
  filter_upwards [] with t
  unfold principalLogWeight gaussianNumerator continuedGaussian
  ring

/-- The contour norm is bounded by its actual square energies with the exact inverse square root scale.
Source P0014 pages 34 and 35, displays 4.13 to 4.15. No numerical energy input is used.
-/
theorem principal_contour_norm_le_energy (δ x : ℝ) (hx : 0 < x) :
    ‖principalContour δ x‖ ≤
      (sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) *
        sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) / (2 * π)) / sqrt x := by
  have heq : principalContour δ x =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        principalLogWeight t * gaussianNumerator δ t *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) := by
    unfold principalContour continuedGaussian principalLogWeight gaussianNumerator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg pi_pos.le]
  rw [heq, norm_mul, hc]
  have hh := norm_integral_mul_cpow_le _ _ LogWeight457.principal_log_weight_memLp_two
    (Numerator457.gaussian_numerator_L2 δ).1 x hx
  calc
    _ ≤ (1 / (2 * π)) *
        (sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) *
          sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) / sqrt x) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- For a fixed real shift the principal contour tends to zero as x tends to infinity.
Source P0014 page 31 display 4.1 and pages 34 and 35, the inverse square root contour remainder.
-/
theorem principal_contour_tendsto_zero (δ : ℝ) :
    Tendsto (principalContour δ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun x : ℝ =>
      (sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) *
        sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) / (2 * π)) / sqrt x)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact principal_contour_norm_le_energy δ x (by linarith)

end LeanLab.HelfgottMajor.Convergence457

#print axioms LeanLab.HelfgottMajor.Convergence457.principal_contour_integrable
#print axioms LeanLab.HelfgottMajor.Convergence457.principal_contour_norm_le_energy
#print axioms LeanLab.HelfgottMajor.Convergence457.principal_contour_tendsto_zero

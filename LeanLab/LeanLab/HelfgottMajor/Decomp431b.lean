import LeanLab.HelfgottMajor.Fourier431
import LeanLab.HelfgottMajor.Mellin389
import LeanLab.HelfgottMajor.Energy389

/-!
The first Plancherel energy estimate on book Part IV page 434.
The Fourier integral is identified with the abstract L2 isometry in Fourier431.
The original sealed energy leaf is unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431b
open Real MeasureTheory Mellin389 Decomp389b
open scoped FourierTransform

/-- The Gaussian critical line energy is integrable.
Source book page 434, first Plancherel display after 16.26.
-/
theorem gaussian_line_integrable (δ : ℝ) :
    Integrable (fun t : ℝ => ‖Decomp269a.gaussianMellin δ
      ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) := by
  have hf := Fourier431.fourier_memLp_two (logGaussian_integrable δ) (logGaussian_memLp_two δ)
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hc := hi.comp_div (by positivity : (2 * π : ℝ) ≠ 0)
  simpa only [mellin_eq_fourier_logGaussian] using hc

/-- The full critical line squared energy equals two pi times nTwo.
Source book page 434, first Plancherel display, and P0014 page 43 display 4.42.
-/
theorem gaussian_line_integral (δ : ℝ) :
    (∫ t : ℝ, ‖Decomp269a.gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) =
      2 * π * Sec45.nTwo := by
  simp_rw [mellin_eq_fourier_logGaussian]
  rw [Measure.integral_comp_div (fun t : ℝ => ‖𝓕 (logGaussian δ) t‖ ^ 2),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π), smul_eq_mul,
    Fourier431.integral_norm_sq_fourier (logGaussian_integrable δ) (logGaussian_memLp_two δ),
    logGaussian_square_integral]

/-- Exactly Decomp389b.gaussian_line_energy_bound.
Source book page 434, Cauchy Schwarz and the first Plancherel display.
-/
theorem gaussian_line_energy_bound (δ : ℝ) :
    sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo := by
  exact Energy389.line_energy_bound_of_full_integral δ (gaussian_line_integrable δ)
    (gaussian_line_integral δ).le

end LeanLab.HelfgottMajor.Decomp431b

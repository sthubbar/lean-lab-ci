import LeanLab.HelfgottMajor.Route669
import LeanLab.HelfgottMajor.Numerator457

/-!
The sharp Gaussian energy for the vertical integral route.
Source P0014 page 35, display 4.15, and page 43, display 4.42.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Energy669
open Real MeasureTheory Set LeanLab.HelfgottArcs Decomp269a Mellin389 Contour457 Weighted457
open MainLemma41Split123
open scoped FourierTransform

/-- P0014 page 35, display 4.15. The Gaussian numerator satisfies the sharp L2 triangle
bound using the two exact Gaussian square moments, without rounding the norms. -/
theorem gaussian_numerator_L2_sharp (δ : ℝ) :
    MemLp (gaussianNumerator δ) 2 ∧
      sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) ≤
        sqrt (2 * π) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) := by
  let f : ℝ → ℂ := fun t => gaussianMellin δ ((3 / 2 : ℂ) + t * Complex.I)
  let g : ℝ → ℂ := fun t => gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)
  let c : ℂ := 2 * π * Complex.I * δ
  have hf : MemLp f 2 := weighted_line_memLp_two δ
  have hg : MemLp g 2 := by
    have hfourier := Fourier431.fourier_memLp_two
      (logGaussian_integrable δ) (logGaussian_memLp_two δ)
    have hi := (memLp_two_iff_integrable_sq_norm hfourier.aestronglyMeasurable).mp hfourier
    have hscaled := hi.comp_div (by positivity : (2 * π : ℝ) ≠ 0)
    have hc : Continuous (𝓕 (logGaussian δ)) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ (logGaussian_integrable δ)
    have hcont : Continuous (fun t : ℝ => 𝓕 (logGaussian δ) (t / (2 * π))) :=
      hc.comp (by fun_prop)
    dsimp only [g]
    simp_rw [mellin_eq_fourier_logGaussian]
    exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr hscaled
  have hE : (∫ t : ℝ, ‖g t‖ ^ 2) = 2 * π * (sqrt π / 2) := by
    simp_rw [g, mellin_eq_fourier_logGaussian]
    rw [Measure.integral_comp_div (fun t : ℝ => ‖𝓕 (logGaussian δ) t‖ ^ 2),
      abs_of_pos (by positivity : 0 < 2 * π), smul_eq_mul,
      Fourier431.integral_norm_sq_fourier
        (logGaussian_integrable δ) (logGaussian_memLp_two δ),
      logGaussian_square_integral]
    rfl
  have hid : gaussianNumerator δ = f - c • g := by
    funext t
    dsimp only [gaussianNumerator, f, g, c, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    congr 2 <;> ring
  have hN : MemLp (gaussianNumerator δ) 2 := hid ▸ hf.sub (hg.const_smul c)
  refine ⟨hN, ?_⟩
  have hnorm (v : ℝ → ℂ) (hv : MemLp v 2) :
      lpNorm v 2 volume = sqrt (∫ t : ℝ, ‖v t‖ ^ 2) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hv.aestronglyMeasurable]
    norm_num [sqrt_eq_rpow]
  have htri := lpNorm_sub_le (g := c • g) hf (by norm_num : (1 : ENNReal) ≤ 2)
  rw [← hid, hnorm _ hN, lpNorm_const_smul, hnorm _ hf, hnorm _ hg] at htri
  have hc : (‖c‖₊ : ℝ) = 2 * π * |δ| := by
    simp [c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [hc, weighted_line_integral δ, hE, sqrt_mul (by positivity : 0 ≤ 2 * π),
    sqrt_mul (by positivity : 0 ≤ 2 * π)] at htri
  simpa only [Sec45.nTwo, mul_add, mul_assoc, mul_left_comm, mul_comm] using htri

/-- P0014 pages 34 and 35, displays 4.13 to 4.15. CONDITIONAL ON hL and hbudget, the
square integrability and quantitative energy bound for the logarithmic derivative. The
Gaussian energy is supplied unconditionally by gaussian_numerator_L2_sharp. -/
theorem vertical_integral_bound_of_log_energy (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ)
    (hL : MemLp (fun τ : ℝ =>
      (deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)) 2)
    (hbudget : sqrt (∫ τ : ℝ,
      ‖(deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)‖ ^ 2) ≤ sqrt (2 * π) * (log q + 6.01)) :
    (2 * π)⁻¹ * ∫ τ : ℝ,
        ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
            DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
          contMellin δ (-1 / 2 + τ * Complex.I)‖ ≤
      (log q + 6.01) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo) := by
  let f : ℝ → ℂ := fun τ =>
      (deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)
  have hG := gaussian_numerator_L2_sharp δ
  have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := volume) (f := f) (g := gaussianNumerator δ)
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (by simpa [f] using hL) (by simpa using hG.1)
  simp only [rpow_two, ← sqrt_eq_rpow] at hcs
  have heq : (∫ τ : ℝ,
        ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
            DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
          contMellin δ (-1 / 2 + τ * Complex.I)‖) =
      ∫ τ : ℝ, ‖f τ‖ * ‖gaussianNumerator δ τ‖ := by
    apply integral_congr_ae
    filter_upwards [] with τ
    rw [Route669.contMellin_eq δ _ (by norm_num [Complex.mul_re])]
    rw [← norm_mul]
    congr 1
    dsimp [f, continuedGaussian, gaussianNumerator]
    ring
  rw [heq]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog := Real.log_nonneg hq1
  have hmul := mul_le_mul hbudget hG.2 (sqrt_nonneg _)
    (by positivity : 0 ≤ sqrt (2 * π) * (log (q : ℝ) + 6.01))
  have hp : 0 < 2 * π := by positivity
  have hs : sqrt (2 * π) * sqrt (2 * π) = 2 * π := by
    rw [← sq, sq_sqrt hp.le]
  calc
    (2 * π)⁻¹ * (∫ τ : ℝ, ‖f τ‖ * ‖gaussianNumerator δ τ‖)
        ≤ (2 * π)⁻¹ * ((sqrt (2 * π) * (log q + 6.01)) *
          (sqrt (2 * π) * (sqrt (sqrt π / 4) + 2 * π * |δ| * sqrt Sec45.nTwo))) :=
      mul_le_mul_of_nonneg_left (hcs.trans hmul) (inv_nonneg.mpr hp.le)
    _ = _ := by
      rw [mul_mul_mul_comm, hs]
      field_simp

end LeanLab.HelfgottMajor.Energy669

#print axioms LeanLab.HelfgottMajor.Energy669.gaussian_numerator_L2_sharp
#print axioms LeanLab.HelfgottMajor.Energy669.vertical_integral_bound_of_log_energy

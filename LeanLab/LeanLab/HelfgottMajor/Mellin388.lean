import LeanLab.HelfgottMajor.Gaussian269

/-!
The exponential substitution behind the Mellin to Fourier conversion in P0014 section 2.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.HelfgottMajor.Mellin388
open Real MeasureTheory FourierTransform

/-- Exponential substitution in the Mellin integral.
Source P0014 page 8, displays 2.1 and 2.2 and the paragraph between them.
-/
theorem mellin_eq_exp_integral (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ y : ℝ, Complex.exp ((y : ℂ) * s) * f (exp y) := by
  unfold mellin
  rw [← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with y
  have hlog : Complex.log (exp y : ℂ) = (y : ℂ) := by
    rw [← Complex.ofReal_log (exp_pos y).le, log_exp]
  have hne : (exp y : ℂ) ≠ 0 := by exact_mod_cast (exp_pos y).ne'
  simp only [Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero hne, hlog]
  calc
    _ = ((exp y : ℂ) * Complex.exp ((y : ℂ) * (s - 1))) * f (exp y) := by ring
    _ = Complex.exp ((y : ℂ) + (y : ℂ) * (s - 1)) * f (exp y) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
    _ = _ := by congr 2; ring

/-- The exact Fourier normalization of the Mellin transform on a vertical line.
Source P0014 page 8, the substitution x equal to exp of minus 2 pi v before display 2.2.
-/
theorem mellin_eq_fourier (f : ℝ → ℂ) (σ τ : ℝ) :
    mellin f ((σ : ℂ) + (τ : ℂ) * Complex.I) =
      (2 * π) • 𝓕 (fun v : ℝ => (exp (-2 * π * v * σ) : ℂ) *
        f (exp (-2 * π * v))) τ := by
  let g : ℝ → ℂ := fun y => Complex.exp ((y : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I)) * f (exp y)
  have hscale : (2 * π) • (∫ v : ℝ, g (-(2 * π) * v)) = ∫ y : ℝ, g y := by
    rw [Measure.integral_comp_mul_left, smul_smul, abs_inv, abs_neg,
      abs_of_pos (by positivity : 0 < 2 * π), mul_inv_cancel₀ (by positivity : 2 * π ≠ 0), one_smul]
  rw [mellin_eq_exp_integral]
  change (∫ y : ℝ, g y) = _
  rw [← hscale]
  apply congrArg (fun z : ℂ => (2 * π) • z)
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with v
  have hv : -(2 * π) * v = -2 * π * v := by ring
  simp only [g, hv, smul_eq_mul]
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- The critical line exponential pullback has the expected squared norm factor.
Source P0014 page 8 display 2.2 at sigma equal to one half.
-/
theorem log_pullback_square_integral (f : ℝ → ℂ) :
    (∫ v : ℝ, ‖(exp (-π * v) : ℂ) * f (exp (-2 * π * v))‖ ^ 2) =
      (∫ t in Set.Ioi (0 : ℝ), ‖f t‖ ^ 2) / (2 * π) := by
  have hpoint (v : ℝ) : ‖(exp (-π * v) : ℂ) * f (exp (-2 * π * v))‖ ^ 2 =
      exp (-2 * π * v) * ‖f (exp (-2 * π * v))‖ ^ 2 := by
    have he : exp (-π * v) ^ 2 = exp (-2 * π * v) := by
      rw [pow_two, ← exp_add]
      congr 1
      ring
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (exp_pos _), he]
  simp_rw [hpoint]
  let g : ℝ → ℝ := fun y => exp y * ‖f (exp y)‖ ^ 2
  change (∫ v : ℝ, g ((-2 * π) * v)) = _
  rw [Measure.integral_comp_mul_left]
  have ha : |(-2 * π : ℝ)| = 2 * π := by
    rw [abs_of_neg (by nlinarith [pi_pos] : (-2 : ℝ) * π < 0)]
    ring
  have hsub : (∫ y : ℝ, g y) = ∫ t in Set.Ioi (0 : ℝ), ‖f t‖ ^ 2 := by
    simpa only [g, smul_eq_mul] using (integral_comp_exp (fun t : ℝ => ‖f t‖ ^ 2))
  rw [abs_inv, ha, hsub, smul_eq_mul]
  ring

/-- Mellin Plancherel on the critical line when the exponential pullback is Schwartz.
Source P0014 page 8 display 2.2. The Schwartz condition is an explicit sufficient regularity hypothesis.
This is a continuous integral identity and does not bound a discrete zero sum.
-/
theorem mellin_plancherel_of_schwartz (f : ℝ → ℂ) (g : SchwartzMap ℝ ℂ)
    (hfg : ∀ v : ℝ, g v = (exp (-π * v) : ℂ) * f (exp (-2 * π * v))) :
    (∫ τ : ℝ, ‖mellin f (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) =
      (2 * π) * (∫ t in Set.Ioi (0 : ℝ), ‖f t‖ ^ 2) := by
  have hpull : (g : ℝ → ℂ) = fun v => (exp (-π * v) : ℂ) * f (exp (-2 * π * v)) :=
    funext hfg
  have hm (τ : ℝ) : mellin f (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) =
      (2 * π) • 𝓕 (g : ℝ → ℂ) τ := by
    rw [mellin_eq_fourier]
    have he (v : ℝ) : -2 * π * v * (1 / 2) = -π * v := by ring
    simp_rw [he]
    rw [← hpull]
  have hfourier : (∫ τ : ℝ, ‖𝓕 (g : ℝ → ℂ) τ‖ ^ 2) = ∫ v : ℝ, ‖g v‖ ^ 2 := by
    simpa only [SchwartzMap.fourier_coe] using SchwartzMap.integral_norm_sq_fourier g
  have hnorm : (∫ v : ℝ, ‖g v‖ ^ 2) = (∫ t in Set.Ioi (0 : ℝ), ‖f t‖ ^ 2) / (2 * π) := by
    simpa only [hpull] using log_pullback_square_integral f
  calc
    _ = (2 * π) ^ 2 * ∫ τ : ℝ, ‖𝓕 (g : ℝ → ℂ) τ‖ ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with τ
      rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * π), mul_pow]
    _ = _ := by
      rw [hfourier, hnorm]
      field_simp


end LeanLab.HelfgottMajor.Mellin388

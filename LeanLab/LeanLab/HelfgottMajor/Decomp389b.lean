import LeanLab.HelfgottMajor.Decomp389c

/-!
A supply decomposition of Decomp269b.middle_mass_bound.
Source P0014 book Part IV, pages 433 and 434, Lemma 16.10 and display 16.26.
The book treats positive and negative imaginary parts separately.
The old sealed file stays unchanged. The small qT branch is in Decomp389c.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp389b
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b
open FourierTransform
open scoped SchwartzMap Topology ContDiff ENNReal

/-- The positive parameter half line energy on the critical line, book page 434.
The sign parameter is used only at 1 and minus 1 in the sampling proof.
-/
noncomputable def lineEnergy (δ ε : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2

/-- The derivative energy above height 1 on either sign of the line, book page 434. -/
noncomputable def derivativeEnergy (δ ε : ℝ) : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ),
    ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2

/-! ### Mellin Plancherel on the critical line, for the Gaussian integrand

The two energy leaves below are the sharp forms of
`∫ t, ‖mellin f (1/2 + t I)‖ ^ 2 = 2 * π * ∫ x in Ioi 0, ‖f x‖ ^ 2`
for `f x = exp (-x^2 / 2) * e (δ x)`, respectively for `log • f`. -/

lemma norm_e (t : ℝ) : ‖e t‖ = 1 := by
  rw [e, Complex.norm_exp]
  have h : (2 * (π : ℂ) * Complex.I * (t : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- Pointwise norm of the Gaussian-character integrand. -/
lemma gauss_norm (δ : ℝ) (x : ℝ) :
    ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ = exp (-x ^ 2 / 2) := by
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

lemma gauss_norm_sq (δ : ℝ) (x : ℝ) :
    ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2 = exp (-x ^ 2) := by
  rw [gauss_norm, sq, ← Real.exp_add]
  congr 1
  ring

/-- Pointwise norm of the log-coordinate integrand `f (exp u) * exp (u / 2)`. -/
lemma log_norm (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖
      = exp (u / 2) * exp (-(exp u) ^ 2 / 2) := by
  rw [norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (exp_pos _), Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

lemma log_norm_sq (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = exp u * exp (-(exp u) ^ 2) := by
  rw [log_norm, mul_pow]
  have h1 : exp (u / 2) ^ 2 = exp u := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : exp (-(exp u) ^ 2 / 2) ^ 2 = exp (-(exp u) ^ 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h1, h2]

lemma log_le_exp_abs (δ : ℝ) (u : ℝ) :
    ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ≤ exp (-|u| / 2) := by
  rw [log_norm]
  rcases le_total u 0 with hu | hu
  · have h1 : exp (-(exp u) ^ 2 / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by have := sq_nonneg (exp u); linarith)
    have h2 : exp (u / 2) = exp (-|u| / 2) := by rw [abs_of_nonpos hu]; ring_nf
    rw [h2]
    exact mul_le_of_le_one_right (exp_pos _).le h1
  · have h1 : exp (u / 2) * exp (-(exp u) ^ 2 / 2) = exp (u / 2 - (exp u) ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [h1, abs_of_nonneg hu]
    refine Real.exp_le_exp.mpr ?_
    have he : 1 + 2 * u ≤ (exp u) ^ 2 := by
      have h := add_one_le_exp u
      have hp := exp_pos u
      nlinarith [sq_nonneg (exp u)]
    linarith

lemma integrable_exp_neg_abs_mul {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => exp (-c * |u|)) := by
  have h1 : IntegrableOn (fun u : ℝ => exp (-c * u)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := c)
      (by norm_num) (by norm_num) hc
    simpa using h
  have h2 : IntegrableOn (fun u : ℝ => exp (c * u)) (Set.Iic 0) := by
    have h := h1.comp_neg
    rw [Set.neg_Ioi, neg_zero] at h
    have h' : IntegrableOn (fun u : ℝ => exp (c * u)) (Set.Iio 0) := by
      refine h.congr_fun ?_ measurableSet_Iio
      intro u _
      show exp (-c * -u) = exp (c * u)
      rw [neg_mul_neg]
    exact (integrableOn_Iic_iff_integrableOn_Iio (f := fun u : ℝ => exp (c * u))).mpr h'
  have h3 : IntegrableOn (fun u : ℝ => exp (-c * |u|)) (Set.Ioi 0) := by
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro u hu
    show exp (-c * u) = exp (-c * |u|)
    rw [abs_of_pos (Set.mem_Ioi.mp hu)]
  have h4 : IntegrableOn (fun u : ℝ => exp (-c * |u|)) (Set.Iic 0) := by
    refine h2.congr_fun ?_ measurableSet_Iic
    intro u hu
    show exp (c * u) = exp (-c * |u|)
    rw [abs_of_nonpos (Set.mem_Iic.mp hu), neg_mul_neg]
  have hu : Set.Ioi (0:ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ, iff_true]
    exact lt_or_ge 0 x
  rw [← integrableOn_univ, ← hu]
  exact h3.union h4

lemma log_continuous (δ : ℝ) :
    Continuous (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) := by
  unfold e
  fun_prop

lemma log_integrable (δ : ℝ) :
    Integrable (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) := by
  refine Integrable.mono' (integrable_exp_neg_abs_mul (c := 1 / 2) (by norm_num))
    (log_continuous δ).aestronglyMeasurable ?_
  filter_upwards with u
  rw [show -(1 / 2 : ℝ) * |u| = -|u| / 2 by ring]
  exact log_le_exp_abs δ u

lemma log_memLp (δ : ℝ) :
    MemLp (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) 2 := by
  have hg : MemLp (fun u : ℝ => exp (-|u| / 2)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm
      (by fun_prop : Continuous (fun u : ℝ => exp (-|u| / 2))).aestronglyMeasurable]
    refine (integrable_exp_neg_abs_mul (c := 1) (by norm_num)).congr ?_
    filter_upwards with u
    have hp : (0:ℝ) < exp (-|u| / 2) := exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos hp, sq, ← Real.exp_add]
    congr 1
    rw [show -(1:ℝ) * |u| = -|u| by ring]
    ring
  refine MemLp.mono' hg (log_continuous δ).aestronglyMeasurable ?_
  filter_upwards with u
  exact log_le_exp_abs δ u

/-- `exp u` is positive, so on the critical line the complex power times the
change-of-variables factor is a single exponential. -/
lemma cpow_exp_mul (u t : ℝ) :
    ((exp u : ℝ) : ℂ) * (((exp u : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I) - 1))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) := by
  have hne : Complex.exp (u : ℂ) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero hne,
    Complex.log_exp (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos]), ← Complex.exp_add]
  congr 1
  ring

/-- The Mellin transform of the Gaussian-character integrand on the critical line is the
Fourier integral of its log coordinate transform. -/
theorem mellin_eq_fourier_gauss (δ : ℝ) (t : ℝ) :
    gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)
      = 𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(t / (2 * π))) := by
  rw [show gaussianMellin δ = mellin (fun x : ℝ => (exp (-x ^ 2 / 2) : ℂ) * e (δ * x)) from rfl,
    mellin, fourier_eq']
  rw [← Real.range_exp, ← Set.image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy)]
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_eq_mul, RCLike.real_smul_eq_coe_mul, smul_eq_mul, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos]), Complex.ofReal_exp]
  simp only [inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    abs_of_pos (exp_pos u)]
  have hL : ((exp u : ℝ) : ℂ) *
      (Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I) - 1)) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)) := by
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hR : Complex.exp ((-2 : ℂ) * (π : ℂ) * ((u : ℂ) * -((t : ℝ) / (2 * π) : ℝ)) * Complex.I) *
      (((exp (u / 2) : ℝ) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))
      = Complex.exp ((u : ℂ) * ((1 / 2 : ℂ) + ((t : ℝ) * Complex.I))) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)) := by
    rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp only [← Complex.ofReal_exp]
  exact hL.trans hR.symm


/-! ### Plancherel for the Fourier integral on `L1 ∩ L2`

Ported from the lab's `LeanLab.ExceptionalSet.WindowParseval264` (which uses Mathlib only). -/

theorem wip_fourier_pairing (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2)
    (g : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, g x * 𝓕 f x =
      ∫ x : ℝ, g x * (𝓕 (h₂.toLp f) : Lp ℂ 2) x := by
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ))
    (by fun_prop) g.integrable h₁
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    exact flip_innerₗ ℝ
  rw [hflip] at hswap
  have hd := congrArg (fun d : 𝓢'(ℝ, ℂ) => d g)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  calc
    _ = ∫ x : ℝ, (𝓕 g) x * f x := by
      simpa only [SchwartzMap.fourier_coe, Real.fourier_eq,
        VectorFourier.fourierIntegral, innerₗ_apply_apply, smul_eq_mul] using hswap.symm
    _ = ∫ x : ℝ, (𝓕 g) x * (h₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := by simpa only [smul_eq_mul] using hd

theorem wip_fourierIntegral_ae_eq (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (𝓕 (h₂.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  simpa using wip_fourier_pairing f h₁ h₂ (hc'.toSchwartzMap hg')

theorem wip_integral_norm_sq_coe (u : Lp (α := ℝ) ℂ 2) :
    ∫ x : ℝ, ‖u x‖ ^ 2 = ‖u‖ ^ 2 := by
  have hi := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) u u)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)] at hi
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    using hi.symm

theorem wip_integral_norm_sq_fourier (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    ∫ t : ℝ, ‖𝓕 f t‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  calc
    _ = ∫ t : ℝ, ‖(𝓕 (h₂.toLp f) : Lp ℂ 2 volume) t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [wip_fourierIntegral_ae_eq f h₁ h₂] with t ht
      rw [ht]
    _ = ‖𝓕 (h₂.toLp f)‖ ^ 2 := wip_integral_norm_sq_coe _
    _ = ‖h₂.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x : ℝ, ‖f x‖ ^ 2 := by
      rw [← wip_integral_norm_sq_coe]
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]

/-! ### The `L2` mass in log coordinates -/

lemma log_sq_integral (δ : ℝ) :
    ∫ u : ℝ, ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
      = Sec45.nTwo := by
  have hIoi : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2 = Sec45.nTwo := by
    have h : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2
        = ∫ x in Set.Ioi (0 : ℝ), exp (-x ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact gauss_norm_sq δ x
    rw [h, show (fun x : ℝ => exp (-x ^ 2)) = (fun x : ℝ => exp (-1 * x ^ 2)) from by
      funext x; ring_nf, integral_gaussian_Ioi]
    simp [Sec45.nTwo]
  have himg : ∫ x in Set.Ioi (0 : ℝ), ‖((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))‖ ^ 2
      = ∫ u : ℝ, exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 := by
    rw [← Real.range_exp, ← Set.image_univ]
    rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => Real.exp_injective hxy)]
    simp only [abs_of_pos (exp_pos _), setIntegral_univ]
  have hpt : ∀ u : ℝ,
      ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2
        = exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 := by
    intro u
    rw [log_norm_sq, gauss_norm_sq, smul_eq_mul]
  rw [show (∫ u : ℝ,
      ‖((exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))‖ ^ 2)
      = ∫ u : ℝ, exp u • ‖((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with u
    exact hpt u]
  rw [← himg, hIoi]

lemma integrable_fourier_sq (δ : ℝ) :
    Integrable (fun ξ : ℝ =>
      ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) * ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) ξ‖ ^ 2) := by
  have h2 := log_memLp δ
  have hmem : MemLp ((𝓕 (h2.toLp (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) : Lp ℂ 2 volume) : ℝ → ℂ) 2 := Lp.memLp _
  have hint : Integrable (fun ξ : ℝ =>
      ‖(𝓕 (h2.toLp (fun u : ℝ => (exp (u / 2) : ℂ) *
        ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u)))) : Lp ℂ 2 volume) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem
  refine hint.congr ?_
  filter_upwards [wip_fourierIntegral_ae_eq (fun u : ℝ => (exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (log_integrable δ) (log_memLp δ)] with ξ hξ
  rw [hξ]


lemma integrable_mellin_sq (δ : ℝ) :
    Integrable (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  have hR : (-(1 / (2 * π)) : ℝ) ≠ 0 := by
    have : (0:ℝ) < 1 / (2 * π) := by positivity
    intro h; linarith [neg_eq_zero.mp h]
  have h : Integrable (fun t : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2) :=
    (integrable_comp_mul_left_iff (fun ξ : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) ξ‖ ^ 2) hR).mpr (integrable_fourier_sq δ)
  refine h.congr ?_
  filter_upwards with t
  rw [mellin_eq_fourier_gauss δ t]
  have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
  rw [harg]

lemma fourier_sq_integral (δ : ℝ) :
    ∫ y : ℝ, ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) y‖ ^ 2 = Sec45.nTwo := by
  rw [wip_integral_norm_sq_fourier (fun u : ℝ => (exp (u / 2) : ℂ) *
    ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (log_integrable δ) (log_memLp δ)]
  exact log_sq_integral δ

theorem integral_mellin_sq_gauss (δ : ℝ) :
    ∫ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = 2 * π * Sec45.nTwo := by
  have hpt : ∀ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2 := by
    intro t
    rw [mellin_eq_fourier_gauss δ t]
    have harg : -(t / (2 * π)) = -(1 / (2 * π)) * t := by field_simp
    rw [harg]
  rw [show ∫ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
      = ∫ t : ℝ, ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
          ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) (-(1 / (2 * π)) * t)‖ ^ 2 from by
    apply integral_congr_ae
    filter_upwards with t
    exact hpt t]
  rw [Measure.integral_comp_mul_left (fun y : ℝ => ‖𝓕 (fun u : ℝ => (exp (u / 2) : ℂ) *
      ((exp (-(exp u) ^ 2 / 2) : ℂ) * e (δ * exp u))) y‖ ^ 2)]
  rw [fourier_sq_integral δ]
  have hcoef : |(-(1 / (2 * π)) : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_div, div_one, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  rw [hcoef, smul_eq_mul]

/-- The two sign-split Mellin energies add up to `2 π` times the `L2` mass. -/
theorem line_integral_sum (δ : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2)
      + (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
      = 2 * π * Sec45.nTwo := by
  set F : ℝ → ℝ := fun t => ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 with hF
  have h1 : (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2)
      = ∫ t in Set.Ioi (0 : ℝ), F t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [one_mul]
    rw [hF]
  have himg : Neg.neg '' (Set.Ioi (0:ℝ)) = Set.Iio (0:ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨y, hy, rfl⟩; linarith
    · intro hx; exact ⟨-x, by linarith, by ring⟩
  have hsub : ∫ t in Set.Ioi (0 : ℝ), F (-t) = ∫ t in Set.Iio (0 : ℝ), F t := by
    rw [← himg]
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt)
      (fun x _ y _ hxy => neg_injective hxy)]
    simp
  have h2 : (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
      = ∫ t in Set.Iic (0 : ℝ), F t := by
    rw [show (∫ t in Set.Ioi (0 : ℝ),
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2)
        = ∫ t in Set.Ioi (0 : ℝ), F (-t) from by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [neg_one_mul]
      rw [hF]]
    rw [hsub, integral_Iic_eq_integral_Iio]
  have hInt : Integrable F := integrable_mellin_sq δ
  rw [h1, h2]
  rw [← Set.compl_Ioi (a := (0:ℝ))]
  rw [integral_add_compl measurableSet_Ioi hInt]
  exact integral_mellin_sq_gauss δ

lemma nTwo_pos : 0 < Sec45.nTwo := by
  rw [Sec45.nTwo]; positivity

/-- The square-root splitting, with the total mass supplied as a hypothesis. -/
lemma sqrt_add_sqrt_le_of_sum {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A + B = 2 * π * Sec45.nTwo) :
    sqrt A + sqrt B ≤ 2 * sqrt π * sqrt Sec45.nTwo := by
  have hsA : sqrt A ^ 2 = A := sq_sqrt hA
  have hsB : sqrt B ^ 2 = B := sq_sqrt hB
  have hsπ : sqrt π ^ 2 = π := sq_sqrt pi_pos.le
  have hsN : sqrt Sec45.nTwo ^ 2 = Sec45.nTwo := sq_sqrt nTwo_pos.le
  have hsq : (sqrt A + sqrt B) ^ 2 = A + B + 2 * (sqrt A * sqrt B) := by
    rw [sq]; linarith
  have hprod : 2 * (sqrt A * sqrt B) ≤ A + B := by
    nlinarith [sq_nonneg (sqrt A - sqrt B)]
  have hR : (2 * sqrt π * sqrt Sec45.nTwo) ^ 2 = 4 * π * Sec45.nTwo := by
    nlinarith [hsπ, hsN]
  have hkey : (sqrt A + sqrt B) ^ 2 ≤ (2 * sqrt π * sqrt Sec45.nTwo) ^ 2 := by
    rw [hsq, hR]; linarith
  have h0 : 0 ≤ sqrt A + sqrt B := by positivity
  have h2 : 0 ≤ 2 * sqrt π * sqrt Sec45.nTwo := by positivity
  nlinarith [hkey, h0, h2, sq_nonneg (sqrt A + sqrt B - 2 * sqrt π * sqrt Sec45.nTwo),
    mul_nonneg h0 h2]


/-- LEAF. Book pages 433 and 434, display 16.26 and the following g squared estimate.
This is the zero sampling reduction before either Mellin energy is evaluated.
It uses the two signs separately and keeps both endpoint norms explicit.
-/
theorem middle_sampling_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
        (0.15 * log (q : ℝ) + 3.389) := by
  sorry

/-- LEAF. Book page 434, the first Plancherel estimate after display 16.26.
The Gaussian square moment is display 4.42 on P0014 page 43.
This has no character, zero count or height parameter.
-/
theorem gaussian_line_energy_bound (δ : ℝ) :
    sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo := by
  have hsum := line_integral_sum δ
  have h1 : lineEnergy δ 1 = ∫ t in Set.Ioi (0 : ℝ),
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 * t : ℝ)) * Complex.I)‖ ^ 2 := rfl
  have h2 : lineEnergy δ (-1) = ∫ t in Set.Ioi (0 : ℝ),
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (((-1) * t : ℝ)) * Complex.I)‖ ^ 2 := rfl
  rw [h1, h2]
  exact sqrt_add_sqrt_le_of_sum (by positivity) (by positivity) hsum

/-- LEAF. Book page 434, the differentiated Mellin Plancherel estimate.
The Gaussian log squared moment is display 4.42 on P0014 page 43.
This has no character, zero count or height parameter.
-/
theorem gaussian_derivative_energy_bound (δ : ℝ) :
    sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog := by
  sorry

/-- The book coefficients of Lemma 16.10 are below the older page 40 coefficients.
Only arithmetic is asserted. No zero sampling input is used.
-/
theorem book_coefficients_le :
    sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog ≤
      sqrt Sec45.nTwo + sqrt Sec45.nLog ∧
    6.484 * sqrt π * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo ≤
      17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := by
  have hs1 : (1 : ℝ) ≤ sqrt π := by linarith [Sec45.sqrt_pi_gt]
  have hs2 : sqrt π ≤ (2 : ℝ) := by linarith [Sec45.sqrt_pi_lt]
  have hs0 : 0 < sqrt π := by positivity
  have hN0 := sqrt_nonneg Sec45.nTwo
  have hL0 := sqrt_nonneg Sec45.nLog
  obtain ⟨hC0, hC⟩ := BookP1617.K_bds
  have hCpos : 0 ≤ log (2 * π * sqrt (exp 1)) := by linarith
  have hprod0 : 0 ≤ log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := mul_nonneg hCpos hN0
  have hLge : (0.8 : ℝ) ≤ sqrt Sec45.nLog := by
    have hh := Decomp389c.middle_constant_ge
    linarith
  have hprod : log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo ≤ 2.3378771 * 0.941397 :=
    mul_le_mul hC.le Sec45.sqrt_nTwo_lt.le hN0 (by norm_num)
  constructor
  · have hdiv : sqrt Sec45.nTwo / sqrt π ≤ sqrt Sec45.nTwo := by
      rw [div_le_iff₀ hs0]
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hs1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs2) hL0]
  · have hnonneg : 0 ≤ log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hs2) hL0]

/-- The large qT branch follows from independent sampling and energy inputs.
CONDITIONAL ON those explicit inputs. Book pages 433 and 434.
-/
theorem large_middle_bound_of_inputs (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hsampling : middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
        (0.15 * log (q : ℝ) + 3.389))
    (henergy : sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo)
    (hderiv : sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT0 : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have hsπ : 0 < sqrt π := by positivity
  have hsT := sqrt_nonneg T
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq
  have hlog : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hC : 0 < 2 * π * sqrt (exp 1) := by positivity
  have he : sqrt (exp 1) ≤ exp 2 := by
    have hs : sqrt (exp 1) ≤ 2 := (sqrt_le_iff).mpr ⟨by norm_num, by linarith [exp_one_lt_three]⟩
    have hh : (2 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
    exact hs.trans hh
  have hshift : 0 ≤ log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) := by
    apply log_nonneg
    rw [le_div_iff₀ hC]
    have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * π)
    nlinarith
  have hE : (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) ≤
      sqrt Sec45.nTwo / sqrt π := by
    calc
      _ ≤ (2 * sqrt π * sqrt Sec45.nTwo) / (2 * π) :=
        div_le_div_of_nonneg_right henergy (by positivity)
      _ = _ := by
        rw [show 2 * π = 2 * sqrt π * sqrt π by nlinarith [sq_sqrt pi_pos.le]]
        field_simp
  have hp := Decomp389a.mellin_critical_norm_le δ ((1 / 2 : ℂ) + Complex.I)
    (by norm_num) HalfMoment389.gaussian_half_moment_bound
  have hn := Decomp389a.mellin_critical_norm_le δ ((1 / 2 : ℂ) - Complex.I)
    (by norm_num) HalfMoment389.gaussian_half_moment_bound
  have hmain : middleMass χ δ T ≤
      (sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog) * sqrt T * log ((q : ℝ) * T) +
      (6.484 * sqrt π * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.3 * log (q : ℝ) + 6.778) := by
    calc
      _ ≤ sqrt Sec45.nTwo / sqrt π * sqrt T *
          log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
          (2 * sqrt π * sqrt Sec45.nLog) * (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
          (2 * 2.15581) * (0.15 * log (q : ℝ) + 3.389) := by
        apply hsampling.trans
        gcongr <;> linarith
      _ = _ := by
        rw [log_div hqT0.ne' hC.ne']
        ring
  obtain ⟨hA, hB⟩ := book_coefficients_le
  have ha := mul_le_mul_of_nonneg_right hA (mul_nonneg hsT hlog)
  have hb := mul_le_mul_of_nonneg_right hB hsT
  nlinarith

/-- Exactly Decomp269b.middle_mass_bound, from sampling, two energies and the small count branch.
This assembly has no sorry of its own and invokes no old sorry theorem.
-/
theorem middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  by_cases hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T
  · exact large_middle_bound_of_inputs q χ δ T hT hlarge
      (middle_sampling_bound q χ hχ δ T hT hlarge hzeros)
      (gaussian_line_energy_bound δ) (gaussian_derivative_energy_bound δ)
  · exact Decomp389c.small_middle_mass_bound q χ hχ δ T hT (le_of_not_ge hlarge) hzeros

end LeanLab.HelfgottMajor.Decomp389b

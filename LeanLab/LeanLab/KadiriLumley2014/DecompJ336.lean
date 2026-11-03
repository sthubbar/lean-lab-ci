import Mathlib
import LeanLab.KadiriLumley2014.Decomp92
import LeanLab.PNTPort.ZetaZeros.Sym

namespace LeanLab.KadiriLumley2014.Task336

open Real
open Set
open LeanLab.KadiriLumley2014.Task64
open LeanLab.KadiriLumley2014.Task92

-- We decompose smoothed_explicit_lower

namespace ZetaCountHelpers

open Real Set MeasureTheory intervalIntegral Filter
open LeanLab.KadiriLumley2014.Task64
open LeanLab.KadiriLumley2014.Task92

/-! ### Derivatives of the weight and of the smoothing kernel -/

/-- The polynomial `t ↦ 4 t (1 - t)` and its derivative. -/
private theorem hasDerivAt_weightBase (t : ℝ) :
    HasDerivAt (fun t : ℝ => 4 * t * (1 - t)) (4 - 8 * t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 4 * t) 4 t := by
    simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
  have h := h1.mul h2
  convert h using 1
  ring

/-- Derivative of the weight, for positive `m`. -/
private theorem hasDerivAt_weight {m : ℕ} (_hm : 1 ≤ m) (t : ℝ) :
    HasDerivAt (weight m) ((m : ℝ) * (4 * t * (1 - t)) ^ (m - 1) * (4 - 8 * t)) t := by
  have h := (hasDerivAt_weightBase t).pow m
  have hfun : ((fun t : ℝ => 4 * t * (1 - t)) ^ m : ℝ → ℝ) = weight m := by
    funext s
    simp [weight]
  rwa [hfun] at h

/-- The weight has the value zero at both endpoints. -/
private theorem weight_zero_endpoints {m : ℕ} (hm : 1 ≤ m) : weight m 0 = 0 ∧ weight m 1 = 0 :=
  weight_endpoints (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)

/-- `4 t (1 - t)` stays in `[0, 1]` on the unit interval. -/
private theorem weightBase_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ 4 * t * (1 - t) ∧ 4 * t * (1 - t) ≤ 1 := by
  constructor
  · nlinarith [ht.1, ht.2]
  · nlinarith [ht.1, ht.2, sq_nonneg (t - 1 / 2)]

/-- Pointwise bound on the derivative of the weight on the unit interval. -/
private theorem abs_deriv_weight_le {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(m : ℝ) * (4 * t * (1 - t)) ^ (m - 1) * (4 - 8 * t)| ≤ 4 * m := by
  obtain ⟨h0, h1⟩ := weightBase_mem ht
  have h4 : |4 - 8 * t| ≤ 4 := by
    rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
  have hp : |(4 * t * (1 - t)) ^ (m - 1)| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg h0 _)]
    exact pow_le_one₀ h0 h1
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  calc (m : ℝ) * |(4 * t * (1 - t)) ^ (m - 1)| * |4 - 8 * t|
      ≤ (m : ℝ) * 1 * 4 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg m)) h4 (abs_nonneg _)
        positivity
    _ = 4 * m := by ring


/-! ### An antiderivative of `t ↦ (1 + δ t)^s` -/

/-- Derivative of `t ↦ (1 + δ t)^s` for a positive complex exponent. -/
private theorem hasDerivAt_cpow_affine (δ : ℝ) (s : ℂ) {t : ℝ} (h : 0 < 1 + δ * t) :
    HasDerivAt (fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ s)
      (s * ((1 + δ * t : ℝ) : ℂ) ^ (s - 1) * (δ : ℂ)) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((1 + δ * t : ℝ) : ℂ)) ((δ : ℝ) : ℂ) t := by
    have h2 : HasDerivAt (fun t : ℝ => 1 + δ * t : ℝ → ℝ) δ t := by
      simpa using (hasDerivAt_id t).const_mul δ |>.const_add 1
    simpa using h2.ofReal_comp
  have h3 : HasDerivAt (fun z : ℂ => z ^ s)
      (s * ((1 + δ * t : ℝ) : ℂ) ^ (s - 1)) ((1 + δ * t : ℝ) : ℂ) := by
    simpa using (hasDerivAt_id ((1 + δ * t : ℝ) : ℂ)).cpow_const
      (Complex.ofReal_mem_slitPlane.mpr h)
  convert h3.comp t h1 using 1 <;> rfl

/-- The antiderivative of `t ↦ (1 + δ t)^s` on the unit interval. -/
private noncomputable def cpowAnti (δ : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  ((1 + δ * t : ℝ) : ℂ) ^ (1 + s) / ((δ : ℂ) * (1 + s))

private theorem cpowAnti_deriv {δ : ℝ} (hδ : δ ≠ 0) {s : ℂ} (hs : 1 + s ≠ 0) {t : ℝ}
    (ht : 0 < 1 + δ * t) :
    HasDerivAt (cpowAnti δ s) (((1 + δ * t : ℝ) : ℂ) ^ s) t := by
  have hbase := hasDerivAt_cpow_affine (δ := δ) (s := 1 + s) ht
  have h := hbase.div_const (((δ : ℂ) * (1 + s)))
  have hsub : (1 + s) - 1 = s := by ring
  have hδC : ((δ : ℂ)) ≠ 0 := by exact_mod_cast hδ
  convert h using 1
  · -- the function: `cpowAnti` is the quotient by a constant
    rfl
  · -- the derivative value
    rw [hsub]
    field_simp

/-! ### The integration by parts -/

/-- The norm of the antiderivative on the unit interval. -/
private theorem norm_cpowAnti_le {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖cpowAnti δ s t‖ ≤ (1 + δ) ^ 2 / (δ * ‖1 + s‖) := by
  have hbase_pos : 0 < 1 + δ * t := by nlinarith [ht.1]
  have h1s : 0 < (1 + s).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  have h1s2 : (1 + s).re ≤ 2 := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  have hnorm1 : (0:ℝ) < ‖1 + s‖ := by
    apply norm_pos_iff.mpr
    intro h
    rw [h] at h1s
    simp at h1s
  have hden : 0 < δ * ‖1 + s‖ := mul_pos hδ hnorm1
  have hlt : 1 + δ * t ≤ 1 + δ := by nlinarith [ht.2]
  have hstep1 : (1 + δ * t) ^ (1 + s).re ≤ (1 + δ) ^ (1 + s).re :=
    Real.rpow_le_rpow (by linarith) hlt h1s.le
  have hbase1 : (1:ℝ) ≤ 1 + δ := by linarith
  have hstep2 : (1 + δ) ^ (1 + s).re ≤ (1 + δ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase1 h1s2
  have htwo : (1 + δ) ^ (2 : ℝ) = (1 + δ) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold cpowAnti
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
    Complex.norm_cpow_eq_rpow_re_of_pos hbase_pos]
  refine div_le_div_of_nonneg_right ?_ hden.le
  calc (1 + δ * t) ^ (1 + s).re ≤ (1 + δ) ^ (1 + s).re := hstep1
    _ ≤ (1 + δ) ^ (2 : ℝ) := hstep2
    _ = (1 + δ) ^ 2 := htwo

/-- One integration by parts for the smoothing kernel: the weight vanishes at the
endpoints, so the boundary term drops and the integral of `(1 + δ t)^s` against the
weight costs one factor `1/(δ‖1+s‖)` times the total variation of the weight. -/
private theorem norm_integral_cpow_weight_le (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)‖ ≤
      (1 + δ) ^ 2 * (4 * m) / (δ * ‖1 + s‖) := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  have h1s : 0 < (1 + s).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  have hs1 : 1 + s ≠ 0 := by
    intro h
    rw [h] at h1s
    simp at h1s
  have hnorm1 : (0:ℝ) < ‖1 + s‖ := by
    apply norm_pos_iff.mpr
    intro h; rw [h] at h1s; simp at h1s
  set g : ℝ → ℂ := fun t => ((1 + δ * t : ℝ) : ℂ) ^ s with hg
  set v : ℝ → ℂ := fun t => (weight m t : ℂ) with hv
  set v' : ℝ → ℂ :=
    fun t => (((m : ℝ) * (4 * t * (1 - t)) ^ (m - 1) * (4 - 8 * t) : ℝ) : ℂ) with hv'
  have hP : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), HasDerivAt (cpowAnti δ s) (g t) t := by
    intro t ht
    have ht0 : 0 < t := by
      have h1 : min (0:ℝ) 1 = 0 := min_eq_left (by norm_num)
      rw [h1] at ht
      exact ht.1
    exact cpowAnti_deriv hδ0 hs1 (by nlinarith)
  have hvderiv : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), HasDerivAt v (v' t) t := by
    intro t _
    exact (hasDerivAt_weight hm t).ofReal_comp
  have hcont : Continuous (fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ (1 + s)) :=
    (Complex.continuous_ofReal_cpow_const (y := (1 + s)) h1s).comp
      (by fun_prop : Continuous fun t : ℝ => 1 + δ * t)
  have hPc : ContinuousOn (cpowAnti δ s) (uIcc (0 : ℝ) 1) :=
    (hcont.div_const _).continuousOn
  have hvc : ContinuousOn v (uIcc (0 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp (weight_continuous m)).continuousOn
  have hgcont : Continuous g :=
    (Complex.continuous_ofReal_cpow_const (y := s) hσ).comp
      (by fun_prop : Continuous fun t : ℝ => 1 + δ * t)
  have hgInt : IntervalIntegrable g volume (0 : ℝ) 1 := hgcont.intervalIntegrable _ _
  have hvcont : Continuous (fun t : ℝ => (((m : ℝ) * (4 * t * (1 - t)) ^ (m - 1) * (4 - 8 * t) : ℝ))) := by
    fun_prop
  have hvInt : IntervalIntegrable v' volume (0 : ℝ) 1 :=
    (Complex.continuous_ofReal.comp hvcont).intervalIntegrable _ _
  have key := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hPc hvc hP hvderiv
    hgInt hvInt
  have hbd : cpowAnti δ s 1 * v 1 - cpowAnti δ s 0 * v 0 = 0 := by
    simp [v, (weight_zero_endpoints hm).1, (weight_zero_endpoints hm).2]
  rw [hbd] at key
  have hsplit : (∫ t in (0 : ℝ)..1, (g t * v t + cpowAnti δ s t * v' t))
      = (∫ t in (0 : ℝ)..1, g t * v t) + ∫ t in (0 : ℝ)..1, cpowAnti δ s t * v' t :=
    intervalIntegral.integral_add
      (hgInt.mul_continuousOn hvc) (hPc.intervalIntegrable.mul_continuousOn (Complex.continuous_ofReal.comp hvcont).continuousOn)
  rw [hsplit] at key
  have hgoal : (∫ t in (0 : ℝ)..1, g t * v t) = -∫ t in (0 : ℝ)..1, cpowAnti δ s t * v' t :=
    eq_neg_of_add_eq_zero_left key
  rw [hgoal, norm_neg]
  have hC : (0:ℝ) ≤ (1 + δ) ^ 2 / (δ * ‖1 + s‖) := by
    have : 0 < δ * ‖1 + s‖ := mul_pos hδ hnorm1
    positivity
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖cpowAnti δ s t * v' t‖ ≤ ((1 + δ) ^ 2 / (δ * ‖1 + s‖)) * (4 * (m : ℝ)) := by
    intro t ht
    rw [norm_mul]
    have h1 : ‖cpowAnti δ s t‖ ≤ (1 + δ) ^ 2 / (δ * ‖1 + s‖) := norm_cpowAnti_le hδ hσ hσ1 ht
    have h2 : ‖v' t‖ ≤ 4 * (m : ℝ) := by
      simp only [v', Complex.norm_real, Real.norm_eq_abs]
      exact abs_deriv_weight_le hm ht
    exact mul_le_mul h1 h2 (norm_nonneg _) hC
  have hmono : ‖∫ t in (0 : ℝ)..1, cpowAnti δ s t * v' t‖
      ≤ ((1 + δ) ^ 2 / (δ * ‖1 + s‖)) * (4 * (m : ℝ)) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => cpowAnti δ s t * v' t) (a := (0:ℝ)) (b := 1)
      (C := ((1 + δ) ^ 2 / (δ * ‖1 + s‖)) * (4 * (m : ℝ)))
      (fun x hx => by
        rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        exact hbound x ⟨hx.1.le, hx.2⟩)
    simpa using h
  refine hmono.trans_eq ?_
  rw [show (4 : ℝ) * m = 4 * (m : ℝ) by push_cast; ring]
  ring

/-! ### The weight transform and the norm of the smoothing factor -/

/-- Decay of the weight transform in the imaginary part: two factors of `‖1 + s‖`,
one from the integration by parts and one from `‖1 + s‖ ≥ |im s|`. -/
private theorem norm_weightTransform_le (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖weightTransform m δ s‖ ≤
      (1 + δ) ^ 2 * (4 * m) /
        (δ * ‖1 + s‖ * (∫ t in (0 : ℝ)..1, weight m t)) := by
  have hI := norm_integral_cpow_weight_le m hm hδ hσ hσ1
  have hmass := weight_mass_pos m
  unfold weightTransform
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmass]
  refine (div_le_div_of_nonneg_right hI hmass.le).trans_eq ?_
  rw [div_div]

/-- Uniform bound for the exponential quotient by the imaginary part. -/
private theorem norm_exp_quotient_le_im {s : ℂ} (hs : s ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (him : s.im ≠ 0) :
    ‖(Complex.exp (s * u) - 1) / s‖ ≤ (Real.exp (u * s.re) + 1) / |s.im| := by
  have hnum : ‖Complex.exp (s * u) - 1‖ ≤ Real.exp (u * s.re) + 1 := by
    have h := norm_sub_le (Complex.exp (s * u)) 1
    simpa [Complex.norm_exp, Complex.mul_re, mul_comm] using h
  have himpos : (0:ℝ) < |s.im| := abs_pos.mpr him
  have hnorm : |s.im| ≤ ‖s‖ := by
    simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm s
  rw [norm_div]
  exact div_le_div₀ (by positivity) hnum himpos hnorm

/-- Uniform bound for the exponential quotient, with no condition on the argument. -/
private theorem norm_exp_quotient_le_exp {s : ℂ} (hs : s ≠ 0) {u : ℝ} (hu : 0 ≤ u) (hσ : s.re ≤ 1) :
    ‖(Complex.exp (s * u) - 1) / s‖ ≤ u * Real.exp u := by
  have hint := exp_quotient_norm_integral hs hu
  have hmono : (∫ v in (0 : ℝ)..u, Real.exp (s.re * v)) ≤ ∫ v in (0 : ℝ)..u, Real.exp v := by
    apply intervalIntegral.integral_mono_on hu
    · exact ((by fun_prop : Continuous fun v : ℝ => Real.exp (s.re * v))).intervalIntegrable
        (μ := volume) _ _
    · exact (Real.continuous_exp).intervalIntegrable (μ := volume) _ _
    · intro v hv
      apply Real.exp_le_exp.mpr
      nlinarith [hv.1, hv.2]
  have hval : (∫ v in (0 : ℝ)..u, Real.exp v) = Real.exp u - 1 := by
    rw [integral_exp]
    simp
  have hfin : Real.exp u - 1 ≤ u * Real.exp u := by
    rcases lt_or_ge u 1 with h1 | h1
    · have hb := Real.exp_bound_div_one_sub_of_interval hu h1
      have hpos : 0 < 1 - u := by linarith
      have hb2 : Real.exp u * (1 - u) ≤ 1 := by
        rw [le_div_iff₀ hpos] at hb
        simpa [mul_comm] using hb
      nlinarith [Real.exp_pos u]
    · nlinarith [Real.exp_pos u]
  calc ‖(Complex.exp (s * u) - 1) / s‖ ≤ ∫ v in (0 : ℝ)..u, Real.exp (s.re * v) := hint
    _ ≤ ∫ v in (0 : ℝ)..u, Real.exp v := hmono
    _ = Real.exp u - 1 := hval
    _ ≤ u * Real.exp u := hfin

/-- The crude uniform bound on `smoothingG` in the critical strip. -/
private theorem norm_smoothingG_le_crude {m : ℕ} {δ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 < u)
    {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖smoothingG m δ u s‖ ≤ Real.exp u * (1 + δ / 2) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hs : s ≠ 0 := by
    intro h; rw [h] at hσ; simp at hσ
  have hq := norm_exp_quotient_le_exp hs hu.le hσ1
  have hw := weightTransform_norm_le m hδ hσ hσ1
  unfold smoothingG
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hq' : ‖(Complex.exp (s * u) - 1) / s‖ / (Real.exp u - 1)
      ≤ u * Real.exp u / (Real.exp u - 1) :=
    div_le_div_of_nonneg_right hq he.le
  have hw0 : 0 ≤ ‖weightTransform m δ s‖ := norm_nonneg _
  have hD : (0:ℝ) ≤ 1 + δ / 2 := by linarith
  have hD2 : (0:ℝ) ≤ u * Real.exp u / (Real.exp u - 1) :=
    div_nonneg (mul_nonneg hu.le (Real.exp_pos u).le) he.le
  have hstep : ‖(Complex.exp (s * u) - 1) / s‖ / (Real.exp u - 1) * ‖weightTransform m δ s‖
      ≤ (u * Real.exp u / (Real.exp u - 1)) * (1 + δ / 2) :=
    mul_le_mul hq' hw hw0 hD2
  have hratio : u * Real.exp u / (Real.exp u - 1) ≤ Real.exp u := by
    rw [div_le_iff₀ he]
    have h1 : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
    nlinarith [Real.exp_pos u]
  exact hstep.trans (mul_le_mul_of_nonneg_right hratio hD)


/-! ### Decay of the smoothing factor in the zero ordinate -/

/-- Decay of `smoothingG` along the critical strip: one factor `1/|im s|` from the
exponential quotient and one from the integration by parts in the weight transform. -/
private theorem norm_smoothingG_le_decay (m : ℕ) (hm : 1 ≤ m) {δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u)
    {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) (him : s.im ≠ 0) :
    ‖smoothingG m δ u s‖ ≤
      (Real.exp u + 1) * ((1 + δ) ^ 2 * (4 * (m : ℝ))) /
        ((Real.exp u - 1) * δ * ‖1 + s‖ * (∫ t in (0 : ℝ)..1, weight m t) * |s.im|) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hs : s ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
  have himpos : 0 < |s.im| := abs_pos.mpr him
  have hnorm1 : (0:ℝ) < ‖1 + s‖ := by
    apply norm_pos_iff.mpr
    intro h
    have : (1 + s).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  have hmass := weight_mass_pos m
  have hq0 := norm_exp_quotient_le_im hs hu.le him
  have hexp : Real.exp (u * s.re) ≤ Real.exp u := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hq : ‖(Complex.exp (s * u) - 1) / s‖ ≤ (Real.exp u + 1) / |s.im| :=
    hq0.trans (div_le_div_of_nonneg_right (by linarith [hexp]) himpos.le)
  have hw := norm_weightTransform_le m hm hδ hσ hσ1
  unfold smoothingG
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have h1 : ‖(Complex.exp (s * u) - 1) / s‖ / (Real.exp u - 1)
      ≤ (Real.exp u + 1) / |s.im| / (Real.exp u - 1) :=
    div_le_div_of_nonneg_right hq he.le
  have h2 : (0:ℝ) ≤ (Real.exp u + 1) / |s.im| / (Real.exp u - 1) :=
    div_nonneg (div_nonneg (by positivity) himpos.le) he.le
  have hstep := mul_le_mul h1 hw (norm_nonneg _) h2
  refine hstep.trans_eq ?_
  field_simp

/-- **The smoothing factor decays like `1/(1+|im s|)²` in the critical strip.**  This is
the estimate behind the convergence of the absolute zero sum; on its own it is not
enough, because bounding the sum over zeros also needs a count of the zeros of `ζ`. -/
private theorem exists_smoothingG_decay {m : ℕ} (hm : 2 ≤ m) {δ u : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ 1 →
      ‖smoothingG m δ u s‖ ≤ C / (1 + |s.im|) ^ 2 := by
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hmass := weight_mass_pos m
  have hDpos : (0:ℝ) < 1 + δ / 2 := by linarith
  set B : ℝ := Real.exp u * (1 + δ / 2) with hBdef
  have hBpos : 0 < B := mul_pos (Real.exp_pos u) hDpos
  set M : ℝ := (Real.exp u + 1) * ((1 + δ) ^ 2 * (4 * (m : ℝ))) /
    ((Real.exp u - 1) * δ * (∫ t in (0 : ℝ)..1, weight m t)) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have h1 : 0 < (Real.exp u + 1) := by positivity
    have h2 : 0 < (1 + δ) ^ 2 * (4 * (m : ℝ)) := by positivity
    have h3 : 0 < (Real.exp u - 1) * δ * (∫ t in (0 : ℝ)..1, weight m t) :=
      mul_pos (mul_pos he hδ) hmass
    exact div_pos (mul_pos h1 h2) h3
  refine ⟨4 * M + 4 * B, by positivity, fun s hσ hσ1 => ?_⟩
  have hden : (0:ℝ) < (1 + |s.im|) ^ 2 := by positivity
  rcases lt_or_ge |s.im| 1 with hsmall | hbig
  · -- bounded ordinates: use the crude estimate
    have hcrude := norm_smoothingG_le_crude (m := m) hδ.le hu hσ hσ1
    have hc : B ≤ (4 * M + 4 * B) / (1 + |s.im|) ^ 2 := by
      rw [le_div_iff₀ hden]
      have h1 : (1 + |s.im|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg s.im]
      nlinarith [hBpos, hMpos]
    exact hcrude.trans hc
  · -- large ordinates: the decay estimate
    have him : s.im ≠ 0 := by
      intro h; rw [h] at hbig; simp at hbig; linarith
    have himpos : 0 < |s.im| := abs_pos.mpr him
    have hdec := norm_smoothingG_le_decay m hm1 hδ hu hσ hσ1 him
    have hnorm1 : (0:ℝ) < ‖1 + s‖ := by
      apply norm_pos_iff.mpr
      intro h
      have hre : (1 + s).re = 0 := by rw [h]; simp
      simp only [Complex.add_re, Complex.one_re] at hre
      linarith
    have hge : |s.im| ≤ ‖1 + s‖ := by
      have h := Complex.abs_im_le_norm (1 + s)
      simpa using h
    -- drop the `‖1+s‖` factor and the extra `1` in the denominator
    have hKD : (0:ℝ) ≤ M := hMpos.le
    have hlinv : 1 / (‖1 + s‖ * |s.im|) ≤ 1 / (|s.im| * |s.im|) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hge, himpos]
    have hstep : ‖smoothingG m δ u s‖ ≤ M / |s.im| ^ 2 := by
      refine hdec.trans ?_
      calc (Real.exp u + 1) * ((1 + δ) ^ 2 * (4 * (m : ℝ))) /
            ((Real.exp u - 1) * δ * ‖1 + s‖ * (∫ t in (0 : ℝ)..1, weight m t) * |s.im|)
          = M * (1 / (‖1 + s‖ * |s.im|)) := by
            rw [hMdef]; field_simp
        _ ≤ M * (1 / (|s.im| * |s.im|)) := mul_le_mul_of_nonneg_left hlinv hKD
        _ = M / |s.im| ^ 2 := by field_simp
    have hfin : M / |s.im| ^ 2 ≤ (4 * M + 4 * B) / (1 + |s.im|) ^ 2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < |s.im| ^ 2)]
      rw [div_mul_eq_mul_div, le_div_iff₀ hden]
      have hsq : (1 + |s.im|) ^ 2 ≤ 4 * |s.im| ^ 2 := by nlinarith [hbig]
      nlinarith [hMpos, hBpos]
    exact hstep.trans hfin

/-! ### The zero-count reduction for `lemma2_2_summable` -/

/-- The zeros of `ζ` in the open critical strip: the index type of `zeroSummand`. -/
private abbrev ZeroStrip : Type := {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}

/-- `∑ log n / n²` converges: the comparison series for the band bounds. -/
private theorem summable_log_div_sq :
    Summable (fun n : ℕ => Real.log (((n : ℝ) + 3) + 1) / (1 + ((n : ℝ) + 3)) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 3) ^ ((3 : ℝ) / 2)) := by
    have h0 := (Real.summable_one_div_nat_rpow (p := (3 : ℝ) / 2)).mpr (by norm_num)
    have h1 := (summable_nat_add_iff 3).mpr h0
    simpa [Nat.cast_add] using h1
  refine Summable.of_nonneg_of_le ?_ ?_ (hbase.mul_left (8 * Real.sqrt 2))
  · intro n
    have h1 : (0:ℝ) < (1 + ((n:ℝ) + 3)) ^ 2 := by
      have h : (0:ℝ) < 1 + ((n:ℝ) + 3) := by
        have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      positivity
    have h2 : 0 ≤ Real.log (((n:ℝ) + 3) + 1) :=
      Real.log_nonneg (by
        have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith)
    exact div_nonneg h2 h1.le
  · intro n
    set x : ℝ := (n : ℝ) + 3 with hxdef
    have hx4 : ((n : ℝ) + 3) + 1 = x + 1 := by rw [hxdef]
    rw [hx4]
    have hx0 : 0 ≤ x := by rw [hxdef]; positivity
    have hx3 : (3:ℝ) ≤ x := by
      rw [hxdef]
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hxpos : 0 < x := by linarith
    have hsqq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have hx32 : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
      rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hxpos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    have hlog1 : Real.log (x + 1) ≤ 2 * Real.sqrt (x + 1) := by
      have h := Real.log_le_rpow_div (x := x + 1) (by linarith) (ε := (1:ℝ)/2) (by norm_num)
      rw [← Real.sqrt_eq_rpow] at h
      have hhalf : Real.sqrt (x + 1) / ((1:ℝ)/2) = 2 * Real.sqrt (x + 1) := by
        rw [div_eq_mul_inv, one_div, inv_inv]; ring
      linarith
    have hsqrt : Real.sqrt (x + 1) ≤ Real.sqrt 2 * Real.sqrt x := by
      have hle2 : x + 1 ≤ 2 * x := by linarith
      calc Real.sqrt (x + 1) ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt hle2
        _ = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
    have hlog2 : Real.log (x + 1) ≤ 2 * Real.sqrt 2 * Real.sqrt x := by
      have h2 := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0:ℝ) ≤ 2)
      linarith
    have hsq2 : Real.sqrt x * Real.sqrt x = x := by nlinarith [hsqq]
    rw [hx32, mul_one_div]
    have hx1 : (0:ℝ) < (1 + x) ^ 2 := by
      have : (0:ℝ) < 1 + x := by linarith
      positivity
    have hden : (0:ℝ) < x * Real.sqrt x := by positivity
    rw [div_le_iff₀ hx1, div_mul_eq_mul_div, le_div_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_right hlog2 (by positivity : (0:ℝ) ≤ x * Real.sqrt x)
    refine hmul.trans ?_
    have hkey : (2 * Real.sqrt 2 * Real.sqrt x) * (x * Real.sqrt x) = 2 * Real.sqrt 2 * x ^ 2 := by
      calc (2 * Real.sqrt 2 * Real.sqrt x) * (x * Real.sqrt x)
          = 2 * Real.sqrt 2 * (x * (Real.sqrt x * Real.sqrt x)) := by ring
        _ = 2 * Real.sqrt 2 * (x * x) := by rw [hsq2]
        _ = 2 * Real.sqrt 2 * x ^ 2 := by ring
    rw [hkey]
    have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    nlinarith [sq_nonneg x, Real.sqrt_nonneg 2]

/-- The summand is at most its multiplicity times the decay constant. -/
private theorem zeroSummand_le_mul_decay {m : ℕ} {δ u X D : ℝ} (hX : Real.exp 38 ≤ X)
    (hDpos : 0 < D)
    (hD : ∀ s : ℂ, 0 < s.re → s.re ≤ 1 → ‖smoothingG m δ u s‖ ≤ D / (1 + |s.im|) ^ 2)
    (ρ : ZeroStrip) :
    zeroSummand m δ u X ρ ≤
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (D / (1 + |(ρ : ℂ).im|) ^ 2) := by
  have hX1 : (1:ℝ) ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hre0 : (ρ : ℂ).re - 1 ≤ 0 := by linarith [ρ.property.2.2]
  have hpow : X ^ ((ρ : ℂ).re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 hre0
  have hpow0 : 0 ≤ X ^ ((ρ : ℂ).re - 1) := Real.rpow_nonneg (by linarith) _
  have hmult : (0:ℝ) ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := Nat.cast_nonneg _
  have hG := hD (ρ : ℂ) ρ.property.2.1 ρ.property.2.2.le
  have hDnn : 0 ≤ D / (1 + |(ρ : ℂ).im|) ^ 2 := (norm_nonneg _).trans hG
  have hstep : (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u (ρ : ℂ)‖ ≤
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (D / (1 + |(ρ : ℂ).im|) ^ 2) :=
    mul_le_mul_of_nonneg_left hG hmult
  unfold zeroSummand
  calc (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u (ρ : ℂ)‖ *
        X ^ ((ρ : ℂ).re - 1)
      ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (D / (1 + |(ρ : ℂ).im|) ^ 2) *
        X ^ ((ρ : ℂ).re - 1) := mul_le_mul_of_nonneg_right hstep hpow0
    _ ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (D / (1 + |(ρ : ℂ).im|) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hmult hDnn)
    _ = (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (D / (1 + |(ρ : ℂ).im|) ^ 2) := by ring

/-- A sum over a union of two finsets is at most the sum of the two sums, for a
nonnegative summand. -/
private theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s t : Finset α) (g : α → ℝ)
    (hg : ∀ x, 0 ≤ g x) : ∑ x ∈ s ∪ t, g x ≤ ∑ x ∈ s, g x + ∑ x ∈ t, g x := by
  have hdisj : Disjoint s (t \ s) := disjoint_sdiff_self_right
  have hunion : s ∪ (t \ s) = s ∪ t := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  calc ∑ x ∈ s ∪ t, g x = ∑ x ∈ s ∪ (t \ s), g x := by rw [hunion]
    _ = ∑ x ∈ s, g x + ∑ x ∈ t \ s, g x := Finset.sum_union hdisj
    _ ≤ ∑ x ∈ s, g x + ∑ x ∈ t, g x := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (s := t \ s) (t := t)
          (f := g) Finset.sdiff_subset (fun x _ _ => hg x)
        linarith

/-- A zero whose height is in `[n, n+1)` lies within `1` of `n` or of `-n`. -/
private theorem band_mem_window {y : ℝ} {n : ℕ} (hn : 3 ≤ n) (h1 : (n : ℝ) ≤ |y|)
    (h2 : |y| < (n : ℝ) + 1) : |y - n| ≤ 1 ∨ |y + n| ≤ 1 := by
  rcases le_total 0 y with hy | hy
  · left
    rw [abs_of_nonneg hy] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  · right
    rw [abs_of_nonpos hy] at h1 h2
    rw [abs_le]
    constructor <;> linarith

set_option maxHeartbeats 1000000 in
/-- **`lemma2_2_summable` modulo a zero count.**

The hypothesis `hwindow` counts the zeros of `ζ` in a window of half-width `1`: with
multiplicity, `O(log |t|)` of them near height `t`.  `LeanLab.PNTPort.ZetaZeros.Sym.zero_count`
gives exactly this at half-width `2/5` (five of those windows cover one of these), so it
is an unavailable import rather than a stronger analytic input.  `hlow` is the
finiteness of the zeros of bounded height. -/
private theorem summable_zeroSummand_of_zero_count {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X)
    (hwindow : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
      ∃ hfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ |ρ.im - t| ≤ 1}.Finite,
        ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ C * Real.log |t|)
    (hlow : {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 6}.Finite) :
    Summable (zeroSummand m δ u X) := by
  classical
  obtain ⟨D, hDpos, hD⟩ := exists_smoothingG_decay hm hδ hδ1 hu hu1
  obtain ⟨C, hCpos, hC⟩ := hwindow
  set f : ZeroStrip → ℝ := fun ρ => zeroSummand m δ u X ρ with hf
  set mult : ZeroStrip → ℝ := fun ρ => (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) with hmultdef
  have hfnn : ∀ ρ : ZeroStrip, 0 ≤ f ρ := fun ρ =>
    zeroSummand_nonneg m δ u ((Real.exp_pos 38).le.trans hX) ρ
  have hmultnn : ∀ ρ : ZeroStrip, 0 ≤ mult ρ := fun ρ => Nat.cast_nonneg _
  set k : ZeroStrip → ℕ := fun ρ => ⌊|(ρ : ℂ).im|⌋₊ with hk
  have hfloor_lo : ∀ ρ : ZeroStrip, ((k ρ : ℕ) : ℝ) ≤ |(ρ : ℂ).im| := fun ρ =>
    Nat.floor_le (abs_nonneg _)
  have hfloor_hi : ∀ ρ : ZeroStrip, |(ρ : ℂ).im| < ((k ρ : ℕ) : ℝ) + 1 := fun ρ =>
    Nat.lt_floor_add_one _
  -- the two windows covering one band
  have hW : ∀ n : ℕ, 6 ≤ n → ∃ W1 W2 : Finset ℂ,
      (∀ ρ : ZeroStrip, k ρ = n → ((ρ : ℂ) ∈ W1 ∨ (ρ : ℂ) ∈ W2)) ∧
      (∑ z ∈ W1, (analyticOrderNatAt riemannZeta z : ℝ)) ≤ C * Real.log n ∧
      (∑ z ∈ W2, (analyticOrderNatAt riemannZeta z : ℝ)) ≤ C * Real.log n := by
    intro n hn
    have hnr : (6:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have habs : |(n:ℝ)| = (n:ℝ) := abs_of_nonneg (by linarith)
    have habs' : |-(n:ℝ)| = (n:ℝ) := by rw [abs_neg, habs]
    obtain ⟨hfin1, hb1⟩ := hC (n:ℝ) (by rw [habs]; exact hnr)
    obtain ⟨hfin2, hb2⟩ := hC (-(n:ℝ)) (by rw [habs']; exact hnr)
    refine ⟨hfin1.toFinset, hfin2.toFinset, ?_, ?_, ?_⟩
    · intro ρ hkρ
      have h1 : (n:ℝ) ≤ |(ρ:ℂ).im| := by
        have := hfloor_lo ρ
        rw [hkρ] at this
        exact this
      have h2 : |(ρ:ℂ).im| < (n:ℝ) + 1 := by
        have := hfloor_hi ρ
        rw [hkρ] at this
        exact this
      rcases band_mem_window (by omega : 3 ≤ n) h1 h2 with h | h
      · refine Or.inl ?_
        rw [Set.Finite.mem_toFinset (hfin1)]
        exact ⟨ρ.property.1, h⟩
      · refine Or.inr ?_
        rw [Set.Finite.mem_toFinset (hfin2)]
        refine ⟨ρ.property.1, ?_⟩
        simpa using h
    · simpa [habs] using hb1
    · simpa [habs'] using hb2
  -- the comparison series of the band bounds
  set B : ℕ → ℝ := fun n => (2 * C * D) * (Real.log ((n:ℝ) + 1) / (1 + (n:ℝ)) ^ 2) with hBdef
  have hBsum : Summable B := by
    have hlog : Summable (fun m : ℕ => Real.log ((m:ℝ) + 1) / (1 + (m:ℝ)) ^ 2) :=
      (summable_nat_add_iff 3).mp (by simpa [Nat.cast_add] using summable_log_div_sq)
    rw [hBdef]
    exact hlog.mul_left (2 * C * D)
  have hBnn : ∀ n : ℕ, 0 ≤ B n := by
    intro n
    rw [hBdef]
    have h1 : (0:ℝ) < (1 + (n:ℝ)) ^ 2 := by positivity
    have h2 : 0 ≤ Real.log ((n:ℝ) + 1) :=
      Real.log_nonneg (by
        have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith)
    have h3 : (0:ℝ) ≤ 2 * C * D := by positivity
    exact mul_nonneg h3 (div_nonneg h2 h1.le)
  -- the summand is at most its multiplicity times `D`
  have hfD : ∀ ρ : ZeroStrip, f ρ ≤ mult ρ * D := by
    intro ρ
    have h1 := zeroSummand_le_mul_decay hX hDpos hD ρ
    rw [hmultdef]
    refine h1.trans ?_
    have h0 : (0:ℝ) ≤ |(ρ:ℂ).im| := abs_nonneg _
    have h2 : (1:ℝ) ≤ (1 + |(ρ:ℂ).im|) ^ 2 := by nlinarith
    have h3 : D / (1 + |(ρ:ℂ).im|) ^ 2 ≤ D := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < (1 + |(ρ:ℂ).im|) ^ 2)]
      nlinarith [hDpos]
    exact mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  -- the bound on one height band
  have hbandF : ∀ (n : ℕ), 6 ≤ n → ∀ t : Finset ZeroStrip, (∀ ρ ∈ t, k ρ = n) →
      ∑ ρ ∈ t, f ρ ≤ B n := by
    intro n hn t ht
    obtain ⟨W1, W2, hsub, hb1, hb2⟩ := hW n hn
    have hnr : (6:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hden2 : (0:ℝ) < (1 + (n:ℝ)) ^ 2 := by positivity
    have hmult : ∑ ρ ∈ t, mult ρ ≤ 2 * C * Real.log (n:ℝ) := by
      rw [hmultdef]
      rw [← Finset.sum_image (f := fun z : ℂ => (analyticOrderNatAt riemannZeta z : ℝ))
        (g := fun ρ : ZeroStrip => (ρ : ℂ)) (s := t) (fun a _ b _ hab => Subtype.ext hab)]
      refine (Finset.sum_le_sum_of_subset_of_nonneg
        (s := Finset.image (fun ρ : ZeroStrip => (ρ : ℂ)) t)
        (t := W1 ∪ W2) (f := fun z : ℂ => (analyticOrderNatAt riemannZeta z : ℝ)) ?_ ?_).trans ?_
      · intro z hz
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
        rcases hsub ρ (ht ρ hρ) with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h
      · intro z _ _
        exact Nat.cast_nonneg _
      · have hunion := sum_union_le_of_nonneg W1 W2
          (fun z : ℂ => (analyticOrderNatAt riemannZeta z : ℝ)) (fun z => Nat.cast_nonneg _)
        linarith
    have hpt : ∀ ρ ∈ t, f ρ ≤ mult ρ * (D / (1 + (n:ℝ)) ^ 2) := by
      intro ρ hρ
      refine (zeroSummand_le_mul_decay hX hDpos hD ρ).trans ?_
      rw [hmultdef]
      have hge : (n:ℝ) ≤ |(ρ:ℂ).im| := by
        have h1 := hfloor_lo ρ
        rw [ht ρ hρ] at h1
        exact h1
      have hge0 : (0:ℝ) ≤ |(ρ:ℂ).im| := abs_nonneg _
      have h2 : (1 + (n:ℝ)) ^ 2 ≤ (1 + |(ρ:ℂ).im|) ^ 2 := by nlinarith
      have h3 : (0:ℝ) < (1 + |(ρ:ℂ).im|) ^ 2 := by
        have : (0:ℝ) < 1 + |(ρ:ℂ).im| := by linarith
        positivity
      have h4 : D / (1 + |(ρ:ℂ).im|) ^ 2 ≤ D / (1 + (n:ℝ)) ^ 2 := by
        rw [div_le_iff₀ h3, div_mul_eq_mul_div, le_div_iff₀ hden2]
        nlinarith [hDpos]
      exact mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
    calc ∑ ρ ∈ t, f ρ ≤ ∑ ρ ∈ t, mult ρ * (D / (1 + (n:ℝ)) ^ 2) := Finset.sum_le_sum hpt
      _ = (∑ ρ ∈ t, mult ρ) * (D / (1 + (n:ℝ)) ^ 2) := (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * C * Real.log (n:ℝ)) * (D / (1 + (n:ℝ)) ^ 2) := by
          apply mul_le_mul_of_nonneg_right hmult
          exact div_nonneg hDpos.le hden2.le
      _ ≤ B n := by
          rw [hBdef]
          have hlog : Real.log (n:ℝ) ≤ Real.log ((n:ℝ) + 1) :=
            Real.log_le_log (by linarith) (by linarith)
          have hstep : (2 * C * Real.log (n:ℝ)) * (D / (1 + (n:ℝ)) ^ 2)
              ≤ (2 * C * Real.log ((n:ℝ) + 1)) * (D / (1 + (n:ℝ)) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (div_nonneg hDpos.le hden2.le)
            have h1 : (0:ℝ) ≤ 2 * C := by positivity
            nlinarith [h1, hlog]
          refine hstep.trans (le_of_eq ?_)
          field_simp
  -- the total multiplicity of the zeros of bounded height
  set L : ℝ := ∑ z ∈ hlow.toFinset, (analyticOrderNatAt riemannZeta z : ℝ) with hLdef
  have hsmall : ∀ t : Finset ZeroStrip, (∀ ρ ∈ t, k ρ < 6) → ∑ ρ ∈ t, f ρ ≤ L * D := by
    intro t ht
    have h1 : ∀ ρ ∈ t, |(ρ:ℂ).im| ≤ 6 := by
      intro ρ hρ
      have h2 := hfloor_hi ρ
      have hk2 : k ρ ≤ 5 := by have := ht ρ hρ; omega
      have hk2' : ((k ρ : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hk2
      linarith
    have hmultsum : ∑ ρ ∈ t, mult ρ ≤ L := by
      rw [hmultdef, hLdef]
      rw [← Finset.sum_image (f := fun z : ℂ => (analyticOrderNatAt riemannZeta z : ℝ))
        (g := fun ρ : ZeroStrip => (ρ : ℂ)) (s := t) (fun a _ b _ hab => Subtype.ext hab)]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro z hz
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
        rw [Set.Finite.mem_toFinset (hlow)]
        exact ⟨ρ.property.1, ρ.property.2.1, ρ.property.2.2, h1 ρ hρ⟩
      · intro z _ _
        exact Nat.cast_nonneg _
    calc ∑ ρ ∈ t, f ρ ≤ ∑ ρ ∈ t, mult ρ * D := Finset.sum_le_sum (fun ρ hρ => hfD ρ)
      _ = (∑ ρ ∈ t, mult ρ) * D := (Finset.sum_mul _ _ _).symm
      _ ≤ L * D := mul_le_mul_of_nonneg_right hmultsum hDpos.le
  -- every finite set of zeros is bounded
  refine summable_of_sum_le (f := f) (c := L * D + ∑' n : ℕ, B n) hfnn ?_
  intro u
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := u)
    (p := fun ρ : ZeroStrip => k ρ < 6) (f := f)
  rw [← hsplit]
  have hA : ∑ ρ ∈ u.filter (fun ρ => k ρ < 6), f ρ ≤ L * D :=
    hsmall _ (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hBle : ∑ ρ ∈ u.filter (fun ρ => ¬ k ρ < 6), f ρ ≤ ∑' n : ℕ, B n := by
    set t : Finset ZeroStrip := u.filter (fun ρ => ¬ k ρ < 6) with htset
    have ht3 : ∀ ρ ∈ t, 6 ≤ k ρ := by
      intro ρ hρ
      have := (Finset.mem_filter.mp hρ).2
      omega
    have hdisj : (↑(t.image k) : Set ℕ).PairwiseDisjoint (fun n => t.filter (fun ρ => k ρ = n)) := by
      intro n _ m _ hnm
      simp only [Function.onFun, Finset.disjoint_left]
      intro ρ h1 h2
      exact hnm (by rw [← (Finset.mem_filter.mp h1).2, ← (Finset.mem_filter.mp h2).2])
    have hbu : (t.image k).biUnion (fun n => t.filter (fun ρ => k ρ = n)) = t := by
      ext ρ
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨n, _, hρ⟩
        exact (Finset.mem_filter.mp hρ).1
      · intro hρ
        exact ⟨k ρ, Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩, Finset.mem_filter.mpr ⟨hρ, rfl⟩⟩
    rw [← hbu, Finset.sum_biUnion hdisj]
    have hstep1 : ∑ n ∈ t.image k, ∑ ρ ∈ t.filter (fun ρ => k ρ = n), f ρ
        ≤ ∑ n ∈ t.image k, B n := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hn3 : 6 ≤ n := by
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hn
        exact ht3 ρ hρ
      exact hbandF n hn3 _ (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    exact hstep1.trans (Summable.sum_le_tsum (t.image k) (fun i _ => hBnn i) hBsum)
  linarith

/-- Three half-width-`2/5` windows centred at `t - 3/5`, `t`, `t + 3/5` cover the
half-width-`1` window at `t`. -/
private theorem window_cover {y t : ℝ} (h : |y - t| ≤ 1) :
    |y - (t - 3/5)| ≤ 2/5 ∨ |y - t| ≤ 2/5 ∨ |y - (t + 3/5)| ≤ 2/5 := by
  have hd := abs_le.mp h
  rcases le_total (y - t) (-(1/5)) with h1 | h1
  · left; rw [abs_le]; constructor <;> linarith [hd.1, hd.2]
  rcases le_total (y - t) (1/5) with h2 | h2
  · right; left; rw [abs_le]; constructor <;> linarith [hd.1, hd.2]
  · right; right; rw [abs_le]; constructor <;> linarith [hd.1, hd.2]

set_option maxHeartbeats 1000000 in
/-- **The count in a window of half-width `1`, from the count in windows of half-width
`2/5`.**  This is the form `LeanLab.PNTPort.ZetaZeros.Sym.zero_count` is stated in
(`N(t + 2/5) - N(t - 2/5) ≪ log |t|` for `|t| ≥ 3`); three such windows cover one of
these.  Heights `3 ≤ |t| < 6` are not needed by the reduction, since bands of that
height are covered by finiteness. -/
private theorem window_one_of_window_two_fifths
    (h : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ∃ hfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ |ρ.im - t| ≤ 2 / 5}.Finite,
        ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ C * Real.log |t|) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 6 ≤ |t| →
      ∃ hfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ |ρ.im - t| ≤ 1}.Finite,
        ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ C' * Real.log |t| := by
  classical
  obtain ⟨C, hCpos, hC⟩ := h
  have hC'pos : (0:ℝ) < 6 * C := by linarith
  refine ⟨6 * C, hC'pos, ?_⟩
  intro t ht
  have ht3 : (3:ℝ) ≤ |t| := by linarith
  have hLnn : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  -- a logarithm comparison used twice
  have hlog2u : ∀ u : ℝ, 3 ≤ u → Real.log (u + 1) ≤ 2 * Real.log u := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have hA : u + 1 ≤ 2 * u := by linarith
    have hB : Real.log (u + 1) ≤ Real.log (2 * u) := Real.log_le_log (by linarith) hA
    have hC : Real.log (2 * u) = Real.log 2 + Real.log u :=
      Real.log_mul (by norm_num) (ne_of_gt hu0)
    have hD : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by linarith)
    linarith
  have ht4 : (4:ℝ) ≤ |t| := by linarith
  have hc1 : (3:ℝ) ≤ |t - 3/5| := by
    have h := abs_sub_abs_le_abs_sub t (3/5 : ℝ)
    have h2 : |(3/5 : ℝ)| = 3/5 := by norm_num
    rw [h2] at h
    linarith
  have hc3 : (3:ℝ) ≤ |t + 3/5| := by
    have h := abs_sub_abs_le_abs_sub t (-(3/5) : ℝ)
    have h2 : |(-(3/5) : ℝ)| = 3/5 := by norm_num
    rw [h2] at h
    have h3 : t - (-(3/5) : ℝ) = t + 3/5 := by ring
    rw [h3] at h
    linarith
  obtain ⟨hf1, hb1⟩ := hC (t - 3/5) hc1
  obtain ⟨hf2, hb2⟩ := hC t ht3
  obtain ⟨hf3, hb3⟩ := hC (t + 3/5) hc3
  have hsubS : ∀ z : ℂ, riemannZeta z = 0 → |z.im - t| ≤ 1 →
      z ∈ (({ρ : ℂ | riemannZeta ρ = 0 ∧ |ρ.im - (t - 3/5)| ≤ 2/5} : Set ℂ) ∪
            ({ρ : ℂ | riemannZeta ρ = 0 ∧ |ρ.im - t| ≤ 2/5} ∪
             {ρ : ℂ | riemannZeta ρ = 0 ∧ |ρ.im - (t + 3/5)| ≤ 2/5})) := by
    intro z hz hz1
    rcases window_cover hz1 with h' | h' | h'
    · exact Or.inl ⟨hz, h'⟩
    · exact Or.inr (Or.inl ⟨hz, h'⟩)
    · exact Or.inr (Or.inr ⟨hz, h'⟩)
  have hfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ |ρ.im - t| ≤ 1}.Finite :=
    (hf1.union (hf2.union hf3)).subset (fun z hz => hsubS z hz.1 hz.2)
  refine ⟨hfin, ?_⟩
  have hsub' : hfin.toFinset ⊆ hf1.toFinset ∪ (hf2.toFinset ∪ hf3.toFinset) := by
    intro z hz
    have hz' := (Set.Finite.mem_toFinset hfin).mp hz
    have := hsubS z hz'.1 hz'.2
    simpa only [Finset.mem_union, Set.mem_union, Set.Finite.mem_toFinset] using this
  have e1 : ∑ z ∈ hf1.toFinset, (analyticOrderNatAt riemannZeta z : ℝ) ≤ 2 * C * Real.log |t| := by
    have h1 : Real.log |t - 3/5| ≤ Real.log (|t| + 1) := by
      apply Real.log_le_log (by linarith [abs_nonneg t])
      rw [abs_sub_le_iff]
      constructor <;> linarith [le_abs_self t, neg_abs_le t]
    have h12 : Real.log |t - 3/5| ≤ 2 * Real.log |t| := h1.trans (hlog2u |t| ht3)
    calc ∑ z ∈ hf1.toFinset, (analyticOrderNatAt riemannZeta z : ℝ)
        ≤ C * Real.log |t - 3/5| := hb1
      _ ≤ C * (2 * Real.log |t|) := mul_le_mul_of_nonneg_left h12 hCpos.le
      _ = 2 * C * Real.log |t| := by ring
  have e2 : ∑ z ∈ hf2.toFinset, (analyticOrderNatAt riemannZeta z : ℝ) ≤ 2 * C * Real.log |t| := by
    calc ∑ z ∈ hf2.toFinset, (analyticOrderNatAt riemannZeta z : ℝ) ≤ C * Real.log |t| := hb2
      _ ≤ C * (2 * Real.log |t|) := mul_le_mul_of_nonneg_left (by linarith) hCpos.le
      _ = 2 * C * Real.log |t| := by ring
  have e3 : ∑ z ∈ hf3.toFinset, (analyticOrderNatAt riemannZeta z : ℝ) ≤ 2 * C * Real.log |t| := by
    have h1 : Real.log |t + 3/5| ≤ Real.log (|t| + 1) := by
      apply Real.log_le_log (by linarith [abs_nonneg t])
      have h3 : t + 3/5 = t - (-(3/5) : ℝ) := by ring
      rw [h3, abs_sub_le_iff]
      constructor <;> linarith [le_abs_self t, neg_abs_le t]
    have h32 : Real.log |t + 3/5| ≤ 2 * Real.log |t| := h1.trans (hlog2u |t| ht3)
    calc ∑ z ∈ hf3.toFinset, (analyticOrderNatAt riemannZeta z : ℝ)
        ≤ C * Real.log |t + 3/5| := hb3
      _ ≤ C * (2 * Real.log |t|) := mul_le_mul_of_nonneg_left h32 hCpos.le
      _ = 2 * C * Real.log |t| := by ring
  have hbound1 := sum_union_le_of_nonneg hf1.toFinset (hf2.toFinset ∪ hf3.toFinset)
    (fun z => (analyticOrderNatAt riemannZeta z : ℝ)) (fun z => Nat.cast_nonneg _)
  have hbound2 := sum_union_le_of_nonneg hf2.toFinset hf3.toFinset
    (fun z => (analyticOrderNatAt riemannZeta z : ℝ)) (fun z => Nat.cast_nonneg _)
  have hstep := Finset.sum_le_sum_of_subset_of_nonneg (s := hfin.toFinset)
    (t := hf1.toFinset ∪ (hf2.toFinset ∪ hf3.toFinset))
    (f := fun z : ℂ => (analyticOrderNatAt riemannZeta z : ℝ))
    hsub' (fun z _ _ => Nat.cast_nonneg _)
  have htotal : ∑ z ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta z : ℝ) ≤ 6 * C * Real.log |t| := by
    linarith
  exact htotal

/-! ### The zeros of `ζ` of bounded height are finite

`hlow` in the reduction above is not an analytic input: that the zeros of `ζ` in a bounded
region are finite is the identity theorem plus compactness, all of which Mathlib has. -/

/-- `ζ` is analytic on the half-plane `Re z < 1`. -/
private theorem riemannZeta_analyticOnNhd_halfPlane :
    AnalyticOnNhd ℂ riemannZeta {z : ℂ | z.re < 1} := by
  refine DifferentiableOn.analyticOnNhd ?_
    (isOpen_lt Complex.continuous_re continuous_const)
  intro z hz
  have hz1 : z ≠ 1 := by
    intro h; rw [h] at hz; simp at hz
  exact (differentiableAt_riemannZeta hz1).differentiableWithinAt

/-- Zeros of `ζ` do not accumulate at `1`: near `1` the function is large. -/
private theorem riemannZeta_eventually_ne_zero_near_one :
    ∀ᶠ z in nhdsWithin (1 : ℂ) {(1:ℂ)}ᶜ, riemannZeta z ≠ 0 := by
  have hnorm : ∀ᶠ z in nhdsWithin (1 : ℂ) {(1:ℂ)}ᶜ,
      (1/2 : ℝ) < ‖(z - 1) * riemannZeta z‖ :=
    riemannZeta_residue_one.norm.eventually (eventually_gt_nhds (by norm_num))
  refine hnorm.mono ?_
  intro z hz hzero
  rw [hzero, mul_zero, norm_zero] at hz
  linarith

/-- No point of `ℂ` is an accumulation point of the zeros of `ζ`: the zero set is closed
and discrete.  Inside `Re z < 1` this is the identity theorem (`ζ 0 = -1/2 ≠ 0`), on
`Re z ≥ 1` it is `ζ ≠ 0`, together with the pole at `1`. -/
private theorem riemannZeta_zeros_closed_discrete :
    IsClosed {z : ℂ | riemannZeta z = 0} ∧ IsDiscrete {z : ℂ | riemannZeta z = 0} := by
  rw [isClosed_and_discrete_iff]
  intro x
  rw [Filter.disjoint_principal_right]
  by_cases hx : x.re < 1
  · have hpre : IsPreconnected {z : ℂ | z.re < 1} := (convex_halfSpace_re_lt 1).isPreconnected
    have hnotid : ¬ Set.EqOn riemannZeta 0 {z : ℂ | z.re < 1} := by
      intro h
      have h0 : (0:ℂ) ∈ {z : ℂ | z.re < 1} := by simp
      have := h h0
      rw [riemannZeta_zero] at this
      norm_num at this
    rcases AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected
      riemannZeta_analyticOnNhd_halfPlane hpre with h | h
    · exact absurd h hnotid
    · -- `h`: the nonvanishing set is codiscrete within the half-plane
      have hd := (mem_codiscreteWithin.mp h) x hx
      rw [Filter.disjoint_principal_right] at hd
      have hSU : ({z : ℂ | riemannZeta z ≠ 0} ∪ {z : ℂ | z.re < 1}ᶜ) ∈ nhdsWithin x {x}ᶜ := by
        have e : (({z : ℂ | z.re < 1} \ {z : ℂ | riemannZeta z ≠ 0}))ᶜ
            = ({z : ℂ | riemannZeta z ≠ 0} ∪ {z : ℂ | z.re < 1}ᶜ) := by
          ext w
          simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union, not_and, not_not]
          tauto
        rwa [e] at hd
      have hU : {z : ℂ | z.re < 1} ∈ nhds x :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hx
      have hU' : {z : ℂ | z.re < 1} ∈ nhdsWithin x {x}ᶜ := nhdsWithin_le_nhds hU
      have hInt : (({z : ℂ | riemannZeta z ≠ 0} ∪ {z : ℂ | z.re < 1}ᶜ)
          ∩ {z : ℂ | z.re < 1}) ∈ nhdsWithin x {x}ᶜ := Filter.inter_mem hSU hU'
      have hfin : {z : ℂ | riemannZeta z ≠ 0} ∈ nhdsWithin x {x}ᶜ := by
        refine Filter.mem_of_superset hInt ?_
        intro w hw
        exact hw.1.resolve_right (fun hb => hb hw.2)
      exact hfin
  · push_neg at hx
    rcases eq_or_ne x 1 with rfl | hx1
    · exact riemannZeta_eventually_ne_zero_near_one
    · have hcont : ContinuousAt riemannZeta x := (differentiableAt_riemannZeta hx1).continuousAt
      have hne : riemannZeta x ≠ 0 := riemannZeta_ne_zero_of_one_le_re hx
      have hmem : {z : ℂ | riemannZeta z ≠ 0} ∈ nhds x := hcont.eventually_ne hne
      exact nhdsWithin_le_nhds hmem

/-- **The zeros of `ζ` in the strip and of bounded height are finite.**  This is `hlow`
of the reduction: closed and discrete, intersected with a compact set.  (The strip
condition is needed: the trivial zeros at the negative even integers all have `im = 0`.) -/
private theorem finite_zeros_strip_bounded :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 6}.Finite := by
  obtain ⟨hclosed, hdisc⟩ := riemannZeta_zeros_closed_discrete
  have htend : Tendsto ((↑) : {z : ℂ // riemannZeta z = 0} → ℂ) cofinite (cocompact ℂ) :=
    hclosed.tendsto_coe_cofinite_of_isDiscrete hdisc
  have hK : IsCompact {z : ℂ | |z.re| ≤ 1 ∧ |z.im| ≤ 6} := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    constructor
    · exact (isClosed_le Complex.continuous_re.abs continuous_const).inter
        (isClosed_le Complex.continuous_im.abs continuous_const)
    · refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := 0) (r := 7)) ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      linarith [hz.1, hz.2]
  have hpre := (tendsto_cofinite_cocompact_iff.mp htend)
    ({z : ℂ | |z.re| ≤ 1 ∧ |z.im| ≤ 6} : Set ℂ) hK
  have himg := hpre.image ((↑) : {z : ℂ // riemannZeta z = 0} → ℂ)
  have hrange : Set.range (Subtype.val : {z : ℂ // riemannZeta z = 0} → ℂ)
      = {z : ℂ | riemannZeta z = 0} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩; exact w.2
    · intro hz; exact ⟨⟨z, hz⟩, rfl⟩
  rw [Set.image_preimage_eq_inter_range, hrange] at himg
  refine himg.subset ?_
  intro z hz
  exact ⟨⟨abs_le.mpr ⟨by linarith [hz.2.1], le_of_lt hz.2.2.1⟩, hz.2.2.2⟩, hz.1⟩


set_option maxHeartbeats 1000000 in
/-- **`lemma2_2_summable` from the lab's zero count alone.**  `hzero` is
`LeanLab.PNTPort.ZetaZeros.Sym.zero_count` verbatim: `O(log |t|)` zeros, with
multiplicity, in `|im ρ - t| ≤ 2/5` for `|t| ≥ 3`.  The decay of the summand, the
banding, the summability and the finiteness of the zeros of bounded height are all
proved in this file; only the count is imported. -/
private theorem lemma2_2_summable_of_zero_count {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X)
    (hzero : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
      ∃ hfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ |ρ.im - t| ≤ 2 / 5}.Finite,
        ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ C * Real.log |t|) :
    Summable (zeroSummand m δ u X) :=
  summable_zeroSummand_of_zero_count hm hδ hδ1 hu hu1 hX
    (window_one_of_window_two_fifths hzero) finite_zeros_strip_bounded

end ZetaCountHelpers


/-- LEAF. Page 4 Lemma 2.2 and equations 2.16 to 2.19.
For m ≥ 2, positive delta and u at most 0.0001 and X ≥ exp 38, the absolute zero summand is summable.
The explicit formula cites Ramare and Saouter 2003 Lemma 4. -/
theorem lemma2_2_summable {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) :
    Summable (zeroSummand m δ u X) :=
  ZetaCountHelpers.lemma2_2_summable_of_zero_count hm hδ hδ1 hu hu1 hX
    LeanLab.PNTPort.ZetaZeros.zero_count

/-- LEAF. Page 4 Lemma 2.2 and equations 2.16 to 2.19.
For m ≥ 2, positive delta and u at most 0.0001 and X ≥ exp 38, J is at least exp u minus 1 times X times F0 minus Sigma, minus u divided by twice X.
The explicit formula cites Ramare and Saouter 2003 Lemma 4. -/
theorem lemma2_2_inequality {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) :
    (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) - u / (2 * X) ≤
      psiAverage m δ u X := by sorry

/-- Assembly of smoothed_explicit_lower from the above leaves. -/
theorem smoothed_explicit_lower_assembly {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) :
    Summable (zeroSummand m δ u X) ∧
      (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) - u / (2 * X) ≤
        psiAverage m δ u X :=
  ⟨lemma2_2_summable hm hδ hδ1 hu hu1 hX, lemma2_2_inequality hm hδ hδ1 hu hu1 hX⟩

end LeanLab.KadiriLumley2014.Task336

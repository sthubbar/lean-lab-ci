/-
P0059 arXiv 1407.7902v1 page 5 equations 2.24 and 2.26.
First integration by parts for the actual polynomial weight.
AI wrote this Lean code, CODEX task92, 2026-10-26.
-/
import LeanLab.KadiriLumley2014.G92
import LeanLab.KadiriLumley2014.WeightFirstFactor

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- The affine complex power has the derivative needed for the first parts step. -/
theorem affine_cpow_hasDerivAt {δ t : ℝ} {s : ℂ}
    (hb : 0 < 1 + δ * t) (hσ : 0 < s.re) :
    HasDerivAt (fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ (s + 1))
      ((δ : ℂ) * (s + 1) * ((1 + δ * t : ℝ) : ℂ) ^ s) t := by
  have hs : s + 1 ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp at h
    linarith
  have hd := hasDerivAt_ofReal_cpow_const hb.ne' hs
  have hbase : HasDerivAt (fun t : ℝ => 1 + δ * t) δ t :=
    by simpa using ((hasDerivAt_id t).const_mul δ).const_add 1
  convert hd.scomp t hbase using 1 <;> simp [Function.comp_def, Complex.real_smul, mul_assoc]

/-- Page 5 equation 2.24 at k = 1 before taking norms. -/
theorem weight_integral_parts {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ)
    {s : ℂ} (hσ : 0 < s.re) :
    ((δ : ℂ) * (s + 1)) *
      (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)) =
      -(∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ (s + 1) * (weightD m t : ℂ)) := by
  let f := fun t : ℝ => (weight m t : ℂ)
  let fd := fun t : ℝ => (weightD m t : ℂ)
  let g := fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ (s + 1)
  let gd := fun t : ℝ => ((δ : ℂ) * (s + 1)) * ((1 + δ * t : ℝ) : ℂ) ^ s
  have hf : Continuous f := Complex.continuous_ofReal.comp (weight_continuous m)
  have hfd : Continuous fd := Complex.continuous_ofReal.comp (weightD_continuous m)
  have hg : Continuous g := (Complex.continuous_ofReal_cpow_const (by simp; linarith :
    0 < (s + 1).re)).comp (by fun_prop)
  have hgd : Continuous gd := by
    apply Continuous.const_mul
    exact (Complex.continuous_ofReal_cpow_const hσ).comp (by fun_prop)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (v := g) (u' := fd) (v' := gd) (a := 0) (b := 1)
    hf.continuousOn hg.continuousOn
    (fun t _ => (weight_hasDerivAt m t).ofReal_comp)
    (fun t ht => by
      have ht0 : 0 ≤ t := by simpa using ht.1.le
      have hb : 0 < 1 + δ * t := by positivity
      exact affine_cpow_hasDerivAt hb hσ)
    (hfd.intervalIntegrable _ _) (hgd.intervalIntegrable _ _)
  have hends := weight_endpoints hm
  have hleft : (∫ t in (0 : ℝ)..1, f t * gd t) =
      ((δ : ℂ) * (s + 1)) *
        (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [f, gd]
    ring
  rw [hleft] at hparts
  simpa only [f, fd, g, hends.1, hends.2, Complex.ofReal_zero, zero_mul,
    sub_self, zero_sub, mul_comm] using hparts


/-- The numerator after one integration by parts is bounded by the first
factor of page 5 equation 2.21. -/
theorem derivative_transform_norm (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ}
    (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ (s + 1) * (weightD m t : ℂ)‖ ≤
      (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ 2 * |weightD m t|) := by
  let F := fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ (s + 1) * (weightD m t : ℂ)
  have hFc : Continuous F := by
    apply Continuous.mul
    · exact (Complex.continuous_ofReal_cpow_const (by simp; linarith : 0 < (s + 1).re)).comp (by fun_prop)
    · exact Complex.continuous_ofReal.comp (weightD_continuous m)
  have hB := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := F)
    (by norm_num : (0 : ℝ) ≤ 1)
  refine hB.trans ?_
  apply intervalIntegral.integral_mono_on (by norm_num) (hFc.norm.intervalIntegrable _ _)
    ((by unfold weightD; fun_prop : Continuous (fun t => (1 + δ * t) ^ 2 * |weightD m t|)).intervalIntegrable _ _)
  intro t ht
  have hb : 1 ≤ 1 + δ * t := by nlinarith [ht.1]
  dsimp [F]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + δ * t),
    Complex.norm_real, Real.norm_eq_abs]
  have hpow : (1 + δ * t) ^ (s + 1).re ≤ (1 + δ * t) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hb (by simp; linarith)
  rw [Real.rpow_two] at hpow
  exact mul_le_mul_of_nonneg_right hpow (abs_nonneg _)

/-- Page 5 equation 2.24 at k = 1 for the normalized polynomial weight. -/
theorem weightTransform_norm_first {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ)
    {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) (hτ : 0 < s.im) :
    ‖weightTransform m δ s‖ ≤ firstFactor m δ / (δ * s.im) := by
  have hp := weight_integral_parts hm hδ.le hσ
  have hnorm := congrArg norm hp
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at hnorm
  have hτn : s.im ≤ ‖s + 1‖ := by
    have h := Complex.abs_im_le_norm (s + 1)
    simpa [abs_of_pos hτ] using h
  have hn := derivative_transform_norm m hδ.le hσ hσ1
  have hcoef := mul_le_mul_of_nonneg_left hτn hδ.le
  have hprod := mul_le_mul_of_nonneg_right hcoef
    (norm_nonneg (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)))
  have hsmall : (δ * s.im) *
      ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)‖ ≤
      (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ 2 * |weightD m t|) := by linarith
  unfold weightTransform firstFactor
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_mass_pos m)]
  apply (div_le_div_iff₀ (weight_mass_pos m) (mul_pos hδ hτ)).mpr
  rw [div_mul_cancel₀ _ (weight_mass_pos m).ne']
  nlinarith


/-- Page 5 equation 2.26 for the polynomial weight. -/
theorem smoothingG_norm_first {m : ℕ} (hm : 0 < m) {δ u : ℝ}
    (hδ : 0 < δ) (hu : 0 < u) {s : ℂ}
    (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) (hτ : 0 < s.im) :
    ‖smoothingG m δ u s‖ ≤ firstFactor m δ * (Real.exp (u * s.re) - 1) /
      ((Real.exp u - 1) * s.re * δ * s.im) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hq := exp_quotient_norm_re hσ hu.le
  have hw := weightTransform_norm_first hm hδ hσ hσ1 hτ
  unfold smoothingG
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hdiv := (div_le_div_iff_of_pos_right he).mpr hq
  have hnum : 0 ≤ Real.exp (u * s.re) - 1 := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg hu.le hσ.le)
    linarith
  have hmul := mul_le_mul hdiv hw (norm_nonneg _)
    (div_nonneg (div_nonneg hnum hσ.le) he.le)
  refine hmul.trans_eq ?_
  field_simp

end LeanLab.KadiriLumley2014.Task92

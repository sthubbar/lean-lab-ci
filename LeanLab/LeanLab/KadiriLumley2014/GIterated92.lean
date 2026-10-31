/-
P0059 arXiv 1407.7902v1 page 5 equations 2.24, 2.27 and 2.28.
Repeated integration by parts for the polynomial smoothing transform.
AI wrote this Lean code, CODEX task92, 2026-10-26.
-/
import LeanLab.KadiriLumley2014.GDerivative92
import LeanLab.KadiriLumley2014.WeightAdmissible

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- The integration by parts identity for any lower derivative of the weight. -/
theorem weight_derivative_parts {m j : ℕ} (hj : j < m) {δ : ℝ} (hδ : 0 ≤ δ)
    {s : ℂ} (hσ : 0 < s.re) :
    ((δ : ℂ) * (s + 1)) *
      (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * ((iteratedDeriv j (weight m) t : ℝ) : ℂ)) =
      -(∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ (s + 1) *
        ((iteratedDeriv (j + 1) (weight m) t : ℝ) : ℂ)) := by
  let f := fun t : ℝ => ((iteratedDeriv j (weight m) t : ℝ) : ℂ)
  let fd := fun t : ℝ => ((iteratedDeriv (j + 1) (weight m) t : ℝ) : ℂ)
  let g := fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ (s + 1)
  let gd := fun t : ℝ => ((δ : ℂ) * (s + 1)) * ((1 + δ * t : ℝ) : ℂ) ^ s
  have hjc := (weight_contDiff m).continuous_iteratedDeriv j (by simp)
  have hj1c := (weight_contDiff m).continuous_iteratedDeriv (j + 1) (by simp)
  have hjd := (weight_contDiff m).differentiable_iteratedDeriv j (by simp)
  have hf : Continuous f := Complex.continuous_ofReal.comp hjc
  have hfd : Continuous fd := Complex.continuous_ofReal.comp hj1c
  have hg : Continuous g := (Complex.continuous_ofReal_cpow_const (by simp; linarith :
    0 < (s + 1).re)).comp (by fun_prop)
  have hgd : Continuous gd := by
    apply Continuous.const_mul
    exact (Complex.continuous_ofReal_cpow_const hσ).comp (by fun_prop)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (v := g) (u' := fd) (v' := gd) (a := 0) (b := 1)
    hf.continuousOn hg.continuousOn
    (fun t _ => by
      have hd := (hjd t).hasDerivAt.ofReal_comp
      simpa only [f, fd, iteratedDeriv_succ] using hd)
    (fun t ht => by
      have ht0 : 0 ≤ t := by simpa using ht.1.le
      have hb : 0 < 1 + δ * t := by positivity
      exact affine_cpow_hasDerivAt hb hσ)
    (hfd.intervalIntegrable _ _) (hgd.intervalIntegrable _ _)
  have hleft : (∫ t in (0 : ℝ)..1, f t * gd t) =
      ((δ : ℂ) * (s + 1)) *
        (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s *
          ((iteratedDeriv j (weight m) t : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [f, gd]
    ring
  rw [hleft] at hparts
  simpa only [f, fd, g, weight_iteratedDeriv_zero hj, weight_iteratedDeriv_one hj,
    Complex.ofReal_zero, zero_mul, sub_self, zero_sub, mul_comm] using hparts

/-- Each integration by parts gains one factor delta times the positive ordinate. -/
theorem weight_derivative_norm_step {m j : ℕ} (hj : j < m) {δ : ℝ} (hδ : 0 < δ)
    {s : ℂ} (hσ : 0 < s.re) (hτ : 0 < s.im) :
    (δ * s.im) *
      ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * ((iteratedDeriv j (weight m) t : ℝ) : ℂ)‖ ≤
      ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ (s + 1) *
        ((iteratedDeriv (j + 1) (weight m) t : ℝ) : ℂ)‖ := by
  have hp := congrArg norm (weight_derivative_parts hj hδ.le hσ)
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at hp
  have hτn : s.im ≤ ‖s + 1‖ := by
    simpa [abs_of_pos hτ] using Complex.abs_im_le_norm (s + 1)
  have hcoef := mul_le_mul_of_nonneg_left hτn hδ.le
  rw [← hp]
  exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

/-- Page 5 equation 2.24 before the last norm estimate, for any k at most m. -/
theorem weight_iterated_norm {m k : ℕ} (hk : k ≤ m) {δ : ℝ} (hδ : 0 < δ)
    {s : ℂ} (hσ : 0 < s.re) (hτ : 0 < s.im) :
    (δ * s.im) ^ k *
      ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)‖ ≤
      ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ (s + k) *
        ((iteratedDeriv k (weight m) t : ℝ) : ℂ)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkm : k < m := by omega
    have hσk : 0 < (s + k).re := by simp; positivity
    have hτk : 0 < (s + k).im := by simpa using hτ
    have hstep := weight_derivative_norm_step hkm hδ hσk hτk
    have hprev := mul_le_mul_of_nonneg_left (ih (by omega)) (mul_pos hδ hτ).le
    simp only [Complex.add_im, Complex.natCast_im, add_zero] at hstep
    have hlast : (s + (k : ℂ)) + 1 = s + ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hlast] at hstep
    calc
      _ = (δ * s.im) * ((δ * s.im) ^ k *
          ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)‖) := by ring
      _ ≤ _ := hprev
      _ ≤ _ := hstep


/-- The shifted numerator is bounded by the higher factor of equation 2.21. -/
theorem higher_transform_norm (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ}
    (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) :
    ‖∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ (s + m) *
      ((iteratedDeriv m (weight m) t : ℝ) : ℂ)‖ ≤
      (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ (m + 1) * |iteratedDeriv m (weight m) t|) := by
  let F := fun t : ℝ => ((1 + δ * t : ℝ) : ℂ) ^ (s + m) * ((iteratedDeriv m (weight m) t : ℝ) : ℂ)
  have hσm : 0 < (s + m).re := by simp; positivity
  have hFc : Continuous F := by
    apply Continuous.mul
    · exact (Complex.continuous_ofReal_cpow_const hσm).comp (by fun_prop)
    · exact Complex.continuous_ofReal.comp ((weight_contDiff m).continuous_iteratedDeriv m (by simp))
  have hDc : Continuous (iteratedDeriv m (weight m)) :=
    (weight_contDiff m).continuous_iteratedDeriv m (by simp)
  have htarget : Continuous (fun t : ℝ => (1 + δ * t) ^ (m + 1) * |iteratedDeriv m (weight m) t|) :=
    (by fun_prop : Continuous (fun t : ℝ => (1 + δ * t) ^ (m + 1))).mul hDc.abs
  have hB := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := F)
    (by norm_num : (0 : ℝ) ≤ 1)
  refine hB.trans ?_
  apply intervalIntegral.integral_mono_on (by norm_num) (hFc.norm.intervalIntegrable _ _)
    (htarget.intervalIntegrable _ _)
  intro t ht
  have hb : 1 ≤ 1 + δ * t := by nlinarith [ht.1]
  dsimp [F]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + δ * t),
    Complex.norm_real, Real.norm_eq_abs]
  have hpow : (1 + δ * t) ^ (s + m).re ≤ (1 + δ * t) ^ ((m + 1 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hb (by simp; linarith)
  rw [Real.rpow_natCast] at hpow
  exact mul_le_mul_of_nonneg_right hpow (abs_nonneg _)

/-- Page 5 equation 2.24 at k = m, normalized by the positive mass. -/
theorem weightTransform_norm_higher (m : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) (hτ : 0 < s.im) :
    ‖weightTransform m δ s‖ ≤ higherFactor m δ / (δ ^ m * s.im ^ m) := by
  have hi := weight_iterated_norm (m := m) le_rfl hδ hσ hτ
  have hn := higher_transform_norm m hδ.le hσ hσ1
  have hsmall := hi.trans hn
  rw [mul_pow] at hsmall
  unfold weightTransform higherFactor
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_mass_pos m)]
  apply (div_le_div_iff₀ (weight_mass_pos m) (mul_pos (pow_pos hδ m) (pow_pos hτ m))).mpr
  rw [div_mul_cancel₀ _ (weight_mass_pos m).ne']
  nlinarith

/-- Page 5 equation 2.27 for the polynomial weight. -/
theorem smoothingG_norm_higher_re (m : ℕ) {δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u)
    {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) (hτ : 0 < s.im) :
    ‖smoothingG m δ u s‖ ≤ higherFactor m δ * (Real.exp (u * s.re) - 1) /
      ((Real.exp u - 1) * s.re * δ ^ m * s.im ^ m) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hq := exp_quotient_norm_re hσ hu.le
  have hw := weightTransform_norm_higher m hδ hσ hσ1 hτ
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

/-- Page 5 equation 2.28 for the polynomial weight. -/
theorem smoothingG_norm_higher_im (m : ℕ) {δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u)
    {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re ≤ 1) (hτ : 0 < s.im) :
    ‖smoothingG m δ u s‖ ≤ higherFactor m δ * (Real.exp (u * s.re) + 1) /
      ((Real.exp u - 1) * δ ^ m * s.im ^ (m + 1)) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hq := exp_quotient_norm_im (u := u) hτ
  have hw := weightTransform_norm_higher m hδ hσ hσ1 hτ
  unfold smoothingG
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hdiv := (div_le_div_iff_of_pos_right he).mpr hq
  have hmul := mul_le_mul hdiv hw (norm_nonneg _)
    (by positivity : 0 ≤ (Real.exp (u * s.re) + 1) / s.im / (Real.exp u - 1))
  refine hmul.trans_eq ?_
  rw [pow_succ]
  field_simp

end LeanLab.KadiriLumley2014.Task92

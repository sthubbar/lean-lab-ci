/-
Proofs of two LEAFs of Split1122bAdjQK8.lean, the adjoint function of Nathanson
Theorem 9.4 as quoted by Bordignon, Johnston and Starichkova, arXiv 2207.09452v6,
papers/P0009.pdf, page 6:
* leafB8_ein_asymp, Ein x - log x → γ, Abramowitz and Stegun 5.1.39, as
  leafB8_ein_asymp_1122c;
* leafB8_ein_deriv, the derivative of x e ^ -Ein x, as leafB8_ein_deriv_1122c.
Route: Ein x = (1 - e ^ -x) log x - the integral of e ^ -t log t over [0, x] by parts,
so Ein x - log x = - e ^ -x log x - that integral, which tends to minus the integral over
(0, ∞), equal to γ by Mathlib's eulerMascheroniConstant_eq_neg_integral_log.
Helpers live in the namespace LeanLab.Cai2002.Ein1122c.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bAdjQK8

namespace LeanLab.Cai2002

namespace Ein1122c

open Real Filter Topology
open MeasureTheory Set

lemma one_sub_exp_neg_le (t : ℝ) : 1 - exp (-t) ≤ t := by
  have := Real.add_one_le_exp (-t); linarith

lemma one_sub_exp_neg_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ 1 - exp (-t) := by
  have : exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma f_bounds {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (1 - exp (-t)) / t ∧ (1 - exp (-t)) / t ≤ 1 := by
  refine ⟨div_nonneg (one_sub_exp_neg_nonneg ht) ht, ?_⟩
  rcases ht.eq_or_lt with h | h
  · subst h; simp
  · rw [div_le_one h]; exact one_sub_exp_neg_le t

lemma f_meas : Measurable (fun t : ℝ => (1 - exp (-t)) / t) := by fun_prop

lemma f_ii {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (1 - exp (-t)) / t) volume 0 x := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' f_meas.aestronglyMeasurable ?_
  rw [uIoc_of_le hx]
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
  have := f_bounds (le_of_lt ht.1)
  show ‖(1 - exp (-t)) / t‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2

lemma f_cont {t : ℝ} (ht : t ≠ 0) : ContinuousAt (fun t : ℝ => (1 - exp (-t)) / t) t := by
  fun_prop (disch := exact ht)

lemma ein_abs_le {x : ℝ} (hx : 0 ≤ x) : |einB8 x| ≤ x := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := 1)
    (f := fun t : ℝ => (1 - exp (-t)) / t) (fun t ht => by
      rw [uIoc_of_le hx] at ht
      have := f_bounds (le_of_lt ht.1)
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  simpa [einB8, abs_of_nonneg hx] using this

lemma ein_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt einB8 ((1 - exp (-x)) / x) x := by
  unfold einB8
  exact intervalIntegral.integral_hasDerivAt_right (f_ii hx.le)
    f_meas.stronglyMeasurable.stronglyMeasurableAtFilter (f_cont hx.ne')

/-- The integrand of the Gamma-derivative integral. -/
lemma g_integrableOn :
    IntegrableOn (fun t : ℝ => log t * exp (-t)) (Ioi 0) := by
  by_contra h
  have h1 := Real.eulerMascheroniConstant_eq_neg_integral_log
  rw [integral_undef h] at h1
  have := one_half_lt_eulerMascheroniConstant
  rw [h1] at this; norm_num at this

lemma g_ii {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => log t * exp (-t)) volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact g_integrableOn.mono_set Ioc_subset_Ioi_self

/-- The integration by parts form of Ein, Abramowitz and Stegun 5.1.39 with 5.1.40:
Ein x = (1 - e ^ -x) log x - the integral over [0, x] of e ^ -t log t, for x > 0.
Used only inside the proof of leafB8_ein_asymp_1122c. -/
noncomputable def G (x : ℝ) : ℝ :=
  (1 - exp (-x)) * log x - ∫ t in (0 : ℝ)..x, log t * exp (-t)

lemma u_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (1 - exp (-t)) * log t)
      (exp (-t) * log t + (1 - exp (-t)) * t⁻¹) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - exp (-t)) (exp (-t)) t := by
    have := ((hasDerivAt_neg t).exp).const_sub 1
    simpa using this
  exact h1.mul (Real.hasDerivAt_log ht.ne')

lemma G_sub {e x : ℝ} (he : 0 < e) (hex : e ≤ x) :
    einB8 x - einB8 e = G x - G e := by
  have hx : 0 < x := he.trans_le hex
  have hpos : ∀ t ∈ uIcc e x, 0 < t := fun t ht => by
    rw [uIcc_of_le hex] at ht; exact he.trans_le ht.1
  have hE : einB8 x - einB8 e = ∫ t in e..x, (1 - exp (-t)) / t := by
    unfold einB8; exact intervalIntegral.integral_interval_sub_left (f_ii hx.le) (f_ii he.le)
  have hgI : (∫ t in (0 : ℝ)..x, log t * exp (-t)) - ∫ t in (0 : ℝ)..e, log t * exp (-t)
      = ∫ t in e..x, log t * exp (-t) :=
    intervalIntegral.integral_interval_sub_left (g_ii hx.le) (g_ii he.le)
  have hcont_u' : ContinuousOn (fun t : ℝ => exp (-t) * log t + (1 - exp (-t)) * t⁻¹) (uIcc e x) := by
    intro t ht
    have := (hpos t ht).ne'
    exact (by fun_prop (disch := exact this) :
      ContinuousAt (fun t : ℝ => exp (-t) * log t + (1 - exp (-t)) * t⁻¹) t).continuousWithinAt
  have hcont_g : ContinuousOn (fun t : ℝ => log t * exp (-t)) (uIcc e x) := by
    intro t ht
    have := (hpos t ht).ne'
    exact (by fun_prop (disch := exact this) :
      ContinuousAt (fun t : ℝ => log t * exp (-t)) t).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => u_hasDerivAt (hpos t ht)) hcont_u'.intervalIntegrable
  have hcongr : ∫ t in e..x, (1 - exp (-t)) / t
      = ∫ t in e..x, ((exp (-t) * log t + (1 - exp (-t)) * t⁻¹) - log t * exp (-t)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    ring
  rw [hE, hcongr, intervalIntegral.integral_sub hcont_u'.intervalIntegrable
    hcont_g.intervalIntegrable, hFTC, ← hgI]
  unfold G; ring

lemma G_tendsto_zero : Tendsto G (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun e : ℝ => (1 - exp (-e)) * log e) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun e : ℝ => |log e * e|) (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).abs
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with e (he : 0 < e)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (one_sub_exp_neg_nonneg he.le),
      abs_of_pos he, mul_comm |log e| e]
    exact mul_le_mul_of_nonneg_right (one_sub_exp_neg_le e) (abs_nonneg _)
  have h2 : Tendsto (fun e : ℝ => ∫ t in (0 : ℝ)..e, log t * exp (-t)) (𝓝[>] 0) (𝓝 0) := by
    have hint : IntegrableOn (fun t : ℝ => log t * exp (-t)) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
      exact g_integrableOn.mono_set Ioc_subset_Ioi_self
    have hc := intervalIntegral.continuousOn_primitive_interval hint 0 (by simp)
    have hc' : ContinuousWithinAt (fun e : ℝ => ∫ t in (0 : ℝ)..e, log t * exp (-t)) (Ioi 0) 0 := by
      refine hc.mono_of_mem_nhdsWithin ?_
      rw [uIcc_of_le zero_le_one]
      exact Filter.mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) Ioo_subset_Icc_self
    simpa using hc'.tendsto
  have := h1.sub h2
  rw [sub_zero] at this
  exact this

lemma ein_eq_G {x : ℝ} (hx : 0 < x) : einB8 x = G x := by
  have hlim : Tendsto (fun e => einB8 e - G e) (𝓝[>] 0) (𝓝 0) := by
    have hE : Tendsto einB8 (𝓝[>] 0) (𝓝 0) := by
      have habs : Tendsto (fun e : ℝ => |e|) (𝓝[>] 0) (𝓝 0) := by
        have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      refine squeeze_zero_norm' ?_ habs
      filter_upwards [self_mem_nhdsWithin] with e (he : 0 < e)
      rw [Real.norm_eq_abs, abs_of_pos he]; exact ein_abs_le he.le
    simpa using hE.sub G_tendsto_zero
  have hev : (fun e => einB8 e - G e) =ᶠ[𝓝[>] 0] fun _ => einB8 x - G x := by
    filter_upwards [Ioo_mem_nhdsGT hx] with e he
    have := G_sub he.1 he.2.le
    linarith
  have := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  linarith

/-- Proof of the LEAF leafB8_ein_asymp of Split1122bAdjQK8.lean, statement verbatim:
Ein x - log x → γ, Abramowitz and Stegun 5.1.39, through γ = - the integral of
log t e ^ -t over (0, ∞), Mathlib's eulerMascheroniConstant_eq_neg_integral_log. -/
theorem leafB8_ein_asymp_1122c :
    Tendsto (fun x => einB8 x - log x) atTop (𝓝 eulerMascheroniConstant) := by
  have hA : Tendsto (fun x : ℝ => exp (-x) * log x) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => x * exp (-x)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_ge_atTop 1] with x hx
      exact mul_nonneg (exp_pos _).le (log_nonneg hx)
    · filter_upwards [eventually_ge_atTop 1] with x hx
      rw [mul_comm x]
      exact mul_le_mul_of_nonneg_left ((log_le_sub_one_of_pos (by linarith)).trans (by linarith))
        (exp_pos _).le
  have hB := intervalIntegral_tendsto_integral_Ioi 0 g_integrableOn tendsto_id
  have := hA.neg.sub hB
  rw [Real.eulerMascheroniConstant_eq_neg_integral_log]
  refine (this.congr' ?_).trans_eq (by simp)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [ein_eq_G hx, G]
  simp only [id]
  ring

/-- Proof of the LEAF leafB8_ein_deriv of Split1122bAdjQK8.lean, statement verbatim:
d/dx (x e ^ -Ein x) = e ^ (-x - Ein x) for x > 0, and right continuity at 0. -/
theorem leafB8_ein_deriv_1122c :
    ContinuousWithinAt (fun x => x * exp (-einB8 x)) (Set.Ici 0) 0 ∧
      ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun x => x * exp (-einB8 x)) (exp (-1 * x - einB8 x)) x := by
  constructor
  · have hE : ContinuousWithinAt einB8 (Ici 0) 0 := by
      have habs : Tendsto (fun e : ℝ => |e|) (𝓝[≥] 0) (𝓝 0) := by
        have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ici 0))
        simpa using this
      have h0 : einB8 0 = 0 := by simp [einB8]
      rw [ContinuousWithinAt, h0]
      refine squeeze_zero_norm' ?_ habs
      filter_upwards [self_mem_nhdsWithin] with e (he : 0 ≤ e)
      rw [Real.norm_eq_abs, abs_of_nonneg he]; exact ein_abs_le he
    exact continuousWithinAt_id.mul (Real.continuous_exp.continuousAt.comp_continuousWithinAt hE.neg)
  · intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h : HasDerivAt (fun x => x * exp (-einB8 x))
        (1 * exp (-einB8 x) + x * (exp (-einB8 x) * -((1 - exp (-x)) / x))) x :=
      (hasDerivAt_id' x).mul ((ein_hasDerivAt hx').neg.exp)
    refine h.congr_deriv ?_
    rw [show -1 * x - einB8 x = -x + -einB8 x by ring, Real.exp_add]
    field_simp
    ring

end Ein1122c

/-- q(1) = e ^ -γ for the adjoint function, adjQB8_one of Split1122bAdjQK8.lean, now free of
LEAFs: the same improper FTC argument from the two proofs above. -/
theorem adjQB8_one_1122c : adjQB8 1 = Real.exp (-Real.eulerMascheroniConstant) := by
  obtain ⟨hc, hd⟩ := Ein1122c.leafB8_ein_deriv_1122c
  have hlim : Filter.Tendsto (fun x => x * Real.exp (-einB8 x)) Filter.atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    have h1 : Filter.Tendsto (fun x => Real.exp (-(einB8 x - Real.log x))) Filter.atTop
        (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
      (Real.continuous_exp.tendsto _).comp Ein1122c.leafB8_ein_asymp_1122c.neg
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_sub, Real.exp_sub, Real.exp_log hx, Real.exp_neg, div_eq_mul_inv]
  have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hc hd
    (fun x _ => (Real.exp_pos _).le) hlim
  unfold adjQB8
  rw [this]
  simp

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.Ein1122c.leafB8_ein_asymp_1122c
#print axioms LeanLab.Cai2002.Ein1122c.leafB8_ein_deriv_1122c
#print axioms LeanLab.Cai2002.adjQB8_one_1122c

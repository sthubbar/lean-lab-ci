/-
Proof of the LEAF leafB8_adjQ_ibp of Prove1122bAdjQDeriv8.lean: the integration by parts
identity s times the integral over x > 0 of x exp (- s x - Ein x) equals q(s + 1), for the
adjoint function q of the linear sieve, Nathanson Theorem 9.4, as quoted by Bordignon,
Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6.
Route: F x = x exp (- s x - Ein x) has derivative - s x exp (...) + exp (- (s + 1) x - Ein x)
on (0, ∞), vanishes at 0 and tends to 0 at infinity; integrate over Ioi 0.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122bAdjQDeriv8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

theorem einB8_integrand_bounds_ibp {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (1 - exp (-t)) / t ∧ (1 - exp (-t)) / t ≤ 1 := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp
  · refine ⟨div_nonneg (by linarith [exp_le_one_iff.2 (neg_nonpos.2 ht)]) h.le, ?_⟩
    rw [div_le_one h]
    linarith [add_one_le_exp (-t)]

theorem einB8_integrableOn_ibp (b : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (1 - exp (-t)) / t) (Set.Icc 0 b) := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
    (by fun_prop : Measurable (fun t : ℝ => (1 - exp (-t)) / t)).aestronglyMeasurable ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall ?_)
  intro t ht
  have := einB8_integrand_bounds_ibp ht.1
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

theorem einB8_nonneg_ibp {x : ℝ} (hx : 0 ≤ x) : 0 ≤ einB8 x := by
  unfold einB8
  exact intervalIntegral.integral_nonneg hx (fun t ht => (einB8_integrand_bounds_ibp ht.1).1)

/-- The fundamental theorem for Ein at x > 0. -/
theorem einB8_hasDerivAt_ibp {x : ℝ} (hx : 0 < x) :
    HasDerivAt einB8 ((1 - exp (-x)) / x) x := by
  have hc : ContinuousAt (fun t : ℝ => (1 - exp (-t)) / t) x :=
    ContinuousAt.div (by fun_prop) continuousAt_id hx.ne'
  have := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := x)
    (f := fun t : ℝ => (1 - exp (-t)) / t)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hx.le).2 (einB8_integrableOn_ibp x))
    ((by fun_prop : Measurable (fun t : ℝ => (1 - exp (-t)) / t)).stronglyMeasurable.stronglyMeasurableAtFilter)
    hc
  exact this

theorem einB8_continuousOn_ibp : ContinuousOn einB8 (Set.Ioi 0) := fun x hx =>
  (einB8_hasDerivAt_ibp hx).continuousAt.continuousWithinAt

theorem ibp_meas (s : ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun x => exp (-s * x - einB8 x))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  ContinuousOn.aestronglyMeasurable
    (((continuous_const.mul continuous_id).continuousOn).sub einB8_continuousOn_ibp).rexp
    measurableSet_Ioi

theorem ibp_int_q {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun x => exp (-s * x - einB8 x)) (Set.Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 hs).mono' (ibp_meas s) ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_le_exp.2 (by linarith [einB8_nonneg_ibp (le_of_lt (Set.mem_Ioi.1 hx))])

/-- Step of adjqibp8, proved: integrability of x exp (- s x - Ein x) on (0, ∞) for s > 0, Nathanson
Theorem 9.4 as quoted by BJS arXiv 2207.09452 page 6. Dominated by x exp (- s x), which is
integrable on (0, ∞) by the Gamma integral.
domination by a Gamma type integrand. -/
theorem leafB8_ibp_int_xq (s : ℝ) (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun x => x * exp (-s * x - einB8 x)) (Set.Ioi 0) := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := s)
    (by norm_num) one_pos hs
  simp only [rpow_one] at hg
  refine hg.mono' ?_ ?_
  · exact (continuous_id.aestronglyMeasurable.restrict).mul (ibp_meas s)
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
  intro x hx
  have hx' : 0 < x := hx
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hx' (exp_pos _))]
  exact mul_le_mul_of_nonneg_left
    (exp_le_exp.2 (by linarith [einB8_nonneg_ibp hx'.le])) hx'.le

/-- Step of adjqibp8, proved: decay of x exp (- s x - Ein x) at infinity for s > 0, Nathanson
Theorem 9.4 as quoted by BJS arXiv 2207.09452 page 6. Squeeze 0 ≤ F x ≤ x exp (- s x).
x exp (- s x) tends to 0. -/
theorem leafB8_ibp_tendsto (s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (fun x => x * exp (-s * x - einB8 x)) Filter.atTop (nhds 0) := by
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (Filter.tendsto_id.const_mul_atTop hs)
  have h1 : Filter.Tendsto (fun x : ℝ => s⁻¹ * ((s * x) ^ 1 * exp (-(s * x))))
      Filter.atTop (nhds 0) := by
    simpa using h0.const_mul s⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    exact mul_nonneg hx (exp_pos _).le
  · filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    have : exp (-s * x - einB8 x) ≤ exp (-(s * x)) :=
      exp_le_exp.2 (by linarith [einB8_nonneg_ibp hx])
    calc x * exp (-s * x - einB8 x) ≤ x * exp (-(s * x)) := mul_le_mul_of_nonneg_left this hx
      _ = s⁻¹ * ((s * x) ^ 1 * exp (-(s * x))) := by field_simp

/-- Step of adjqibp8, proved: continuity at 0 from the right of x exp (- s x - Ein x), Nathanson
Theorem 9.4 as quoted by BJS arXiv 2207.09452 page 6. Squeeze |F x| ≤ x on [0, ∞).
squeeze at 0. -/
theorem leafB8_ibp_cont0 (s : ℝ) (hs : 0 < s) :
    ContinuousWithinAt (fun x => x * exp (-s * x - einB8 x)) (Set.Ici 0) 0 := by
  unfold ContinuousWithinAt
  simp only [zero_mul]
  have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ici 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hid ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg hx (exp_pos _).le
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) ≤ x := hx
    have : exp (-s * x - einB8 x) ≤ 1 :=
      exp_le_one_iff.2 (by nlinarith [einB8_nonneg_ibp hx'])
    nlinarith

theorem ibp_hasDeriv {s x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => x * exp (-s * x - einB8 x))
      (-s * (x * exp (-s * x - einB8 x)) + exp (-(s + 1) * x - einB8 x)) x := by
  have hE := einB8_hasDerivAt_ibp hx
  have hg : HasDerivAt (fun x => -s * x - einB8 x) (-s * 1 - (1 - exp (-x)) / x) x :=
    ((hasDerivAt_id x).const_mul (-s)).sub hE
  have h := (hasDerivAt_id' x).mul hg.exp
  convert h using 1
  · have e : exp (-(s + 1) * x - einB8 x) = exp (-x) * exp (-s * x - einB8 x) := by
      rw [← exp_add]; ring_nf
    rw [e]; field_simp; ring

/-- Twin of leafB8_adjQ_ibp of Prove1122bAdjQDeriv8.lean, statement copied verbatim. -/
theorem leafB8_adjQ_ibp_twin (s : ℝ) (hs : 0 < s) :
    s * ∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x) = adjQB8 (s + 1) := by
  have h1 := leafB8_ibp_int_xq s hs
  have h2 := ibp_int_q (s := s + 1) (by linarith)
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (leafB8_ibp_cont0 s hs)
    (fun x hx => ibp_hasDeriv (s := s) (Set.mem_Ioi.1 hx)) ((h1.const_mul (-s)).add h2)
    (leafB8_ibp_tendsto s hs)
  rw [MeasureTheory.integral_add (h1.const_mul (-s)) h2, MeasureTheory.integral_const_mul]
    at key
  unfold adjQB8
  simp only [zero_mul, sub_zero] at key
  linarith
end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_adjQ_ibp_twin

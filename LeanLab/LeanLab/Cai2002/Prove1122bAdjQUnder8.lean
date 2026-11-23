/-
Proof of the LEAF leafB8_adjQ_hasDeriv_under of Prove1122bAdjQDeriv8.lean: differentiation
under the integral sign for the adjoint function q of the linear sieve, Nathanson Theorem 9.4,
as quoted by Bordignon, Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf,
page 6. Here q(s) = the integral over x > 0 of exp (- s x - Ein x).
Route: hasDerivAt_integral_of_dominated_loc_of_deriv_le on the neighbourhood t > s/2 of s,
with bound x exp (- (s/2) x), using 0 ≤ Ein x for x ≥ 0.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122bAdjQDeriv8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- The integrand of Ein, bounds on [0, ∞). -/
theorem einB8u_integrand_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (1 - exp (-t)) / t ∧ (1 - exp (-t)) / t ≤ 1 := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp
  · refine ⟨div_nonneg (by linarith [exp_le_one_iff.2 (neg_nonpos.2 ht)]) h.le, ?_⟩
    rw [div_le_one h]
    linarith [add_one_le_exp (-t)]

theorem einB8u_integrand_measurable :
    Measurable (fun t : ℝ => (1 - exp (-t)) / t) := by
  fun_prop

theorem einB8u_integrableOn (b : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (1 - exp (-t)) / t) (Set.Icc 0 b) := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
    einB8u_integrand_measurable.aestronglyMeasurable ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall ?_)
  intro t ht
  have := einB8u_integrand_bounds ht.1
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

theorem einB8u_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ einB8 x := by
  unfold einB8
  exact intervalIntegral.integral_nonneg hx (fun t ht => (einB8u_integrand_bounds ht.1).1)

theorem einB8u_continuousOn : ContinuousOn einB8 (Set.Ioi 0) := by
  intro x hx
  have hc : ContinuousOn einB8 (Set.Icc 0 (x + 1)) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := x + 1)
      (μ := MeasureTheory.volume) (f := fun t : ℝ => (1 - exp (-t)) / t)
      (by rw [Set.uIcc_of_le (by linarith [(Set.mem_Ioi.1 hx)])]; exact einB8u_integrableOn _)
    rwa [Set.uIcc_of_le (by linarith [(Set.mem_Ioi.1 hx)])] at this
  exact (hc.continuousAt (Icc_mem_nhds (Set.mem_Ioi.1 hx) (by linarith))).continuousWithinAt

theorem adjQB8u_integrand_aesm (t : ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun x => exp (-t * x - einB8 x))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  exact (((continuous_const.mul continuous_id).continuousOn).sub einB8u_continuousOn).rexp

/-- Twin of leafB8_adjQ_hasDeriv_under of Prove1122bAdjQDeriv8.lean, statement copied
verbatim. -/
theorem leafB8_adjQ_hasDeriv_under_twin (s : ℝ) (hs : 0 < s) :
    HasDerivAt adjQB8
      (-∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x)) s := by
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hs2 : 0 < s / 2 := by linarith
  -- integrability of exp (- s x - Ein x)
  have hint : MeasureTheory.Integrable (fun x => exp (-s * x - einB8 x)) μ := by
    refine (exp_neg_integrableOn_Ioi 0 hs).mono' (adjQB8u_integrand_aesm s) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall ?_)
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.2 (by linarith [einB8u_nonneg (le_of_lt hx)])
  have hF'meas : MeasureTheory.AEStronglyMeasurable
      (fun x => -x * exp (-s * x - einB8 x)) μ := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (continuous_neg.continuousOn).mul
      (((continuous_const.mul continuous_id).continuousOn).sub einB8u_continuousOn).rexp
  have hbound : MeasureTheory.Integrable (fun x : ℝ => x * exp (-(s / 2) * x)) μ := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := s / 2)
      (by norm_num) one_pos hs2
    simp only [Real.rpow_one] at this
    exact this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t x => exp (-t * x - einB8 x))
    (F' := fun t x => -x * exp (-t * x - einB8 x))
    (bound := fun x => x * exp (-(s / 2) * x)) (x₀ := s)
    (Ioi_mem_nhds (show s / 2 < s by linarith))
    (Filter.Eventually.of_forall (fun t => adjQB8u_integrand_aesm t)) hint hF'meas ?_ hbound ?_
  · have h2 := key.2
    have e : (∫ x, (fun t x => -x * exp (-t * x - einB8 x)) s x ∂μ)
        = -∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x) := by
      simp only [neg_mul]
      exact MeasureTheory.integral_neg _
    rw [e] at h2
    exact h2
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall ?_)
    intro x hx t ht
    have hx0 : 0 < x := hx
    have ht' : s / 2 < t := ht
    rw [Real.norm_eq_abs, neg_mul, abs_neg, abs_of_pos (mul_pos hx0 (exp_pos _))]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) hx0.le
    nlinarith [einB8u_nonneg hx0.le]
  · refine Filter.Eventually.of_forall ?_
    intro x t _
    have h1 : HasDerivAt (fun t => -t * x - einB8 x) (-x) t := by
      have := ((hasDerivAt_id t).neg.mul_const x).sub_const (einB8 x)
      simpa using this
    have := h1.exp
    simpa [mul_comm] using this

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_adjQ_hasDeriv_under_twin

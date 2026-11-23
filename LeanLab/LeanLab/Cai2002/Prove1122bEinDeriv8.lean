/-
Twin proof of the LEAF leafB8_ein_deriv of Split1122bAdjQK8.lean: the map x ↦ x exp (- Ein x)
is continuous within Ici 0 at 0 and has derivative exp (- x - Ein x) on (0, ∞), for the
adjoint function of the linear sieve, Nathanson Theorem 9.4, as quoted by Bordignon,
Johnston and Starichkova, arXiv 2207.09452, page 6.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bAdjQK8

open Real

noncomputable section

namespace LeanLab.Cai2002

theorem einB8_integrand_bounds_ed {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (1 - exp (-t)) / t ∧ (1 - exp (-t)) / t ≤ 1 := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp
  · refine ⟨div_nonneg (by linarith [exp_le_one_iff.2 (neg_nonpos.2 ht)]) h.le, ?_⟩
    rw [div_le_one h]
    linarith [add_one_le_exp (-t)]

theorem einB8_integrableOn_ed (b : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (1 - exp (-t)) / t) (Set.Icc 0 b) := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
    (by fun_prop : Measurable (fun t : ℝ => (1 - exp (-t)) / t)).aestronglyMeasurable ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall ?_)
  intro t ht
  have := einB8_integrand_bounds_ed ht.1
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

theorem einB8_nonneg_ed {x : ℝ} (hx : 0 ≤ x) : 0 ≤ einB8 x := by
  unfold einB8
  exact intervalIntegral.integral_nonneg hx (fun t ht => (einB8_integrand_bounds_ed ht.1).1)

theorem einB8_hasDerivAt_ed {x : ℝ} (hx : 0 < x) :
    HasDerivAt einB8 ((1 - exp (-x)) / x) x := by
  have hc : ContinuousAt (fun t : ℝ => (1 - exp (-t)) / t) x :=
    ContinuousAt.div (by fun_prop) continuousAt_id hx.ne'
  have := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := x)
    (f := fun t : ℝ => (1 - exp (-t)) / t)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hx.le).2 (einB8_integrableOn_ed x))
    ((by fun_prop : Measurable (fun t : ℝ => (1 - exp (-t)) / t)).stronglyMeasurable.stronglyMeasurableAtFilter)
    hc
  exact this

theorem leafB8_ein_deriv_twin :
    ContinuousWithinAt (fun x => x * exp (-einB8 x)) (Set.Ici 0) 0 ∧
      ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun x => x * exp (-einB8 x)) (exp (-1 * x - einB8 x)) x := by
  refine ⟨?_, ?_⟩
  · rw [ContinuousWithinAt, zero_mul]
    have hup : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ici 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_nonneg hx (exp_pos _).le
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : (0 : ℝ) ≤ x := hx
      have : exp (-einB8 x) ≤ 1 := exp_le_one_iff.2 (neg_nonpos.2 (einB8_nonneg_ed hx'))
      calc x * exp (-einB8 x) ≤ x * 1 := mul_le_mul_of_nonneg_left this hx'
        _ = x := mul_one x
  · intro x hx
    have hx' : 0 < x := hx
    have hd := (hasDerivAt_id' x).mul ((einB8_hasDerivAt_ed hx').neg.exp)
    have hne : x ≠ 0 := hx'.ne'
    have heq : 1 * exp (-einB8 x) + x * (exp (-einB8 x) * -((1 - exp (-x)) / x))
        = exp (-1 * x - einB8 x) := by
      rw [show -1 * x - einB8 x = -x + -einB8 x by ring, exp_add]
      field_simp
      ring
    exact hd.congr_deriv heq

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_ein_deriv_twin

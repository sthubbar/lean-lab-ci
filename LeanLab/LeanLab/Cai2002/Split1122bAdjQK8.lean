/-
Split of the LEAF leafB8_adjQ_K of Split1122bAdjoint8.lean: K(q) = e ^ -γ for the explicit
adjoint function q of Nathanson Theorem 9.4, as quoted by Bordignon, Johnston and
Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6.
Argument: with p(t) = 0 on (0, 1), p(t) = 1 / t on [1, 2], p(t) = (1 + log (t - 1)) / t on
[2, 3], one has (s p(s))' = p(s - 1), so the adjoint pairing s p(s) q(s) plus the integral
of p(t) q(t + 1) over [s - 1, s] is constant on [1, 3]; at s = 3 it is K(q), at s = 1 it is
q(1). Then d/dx (x e ^ -Ein x) = e ^ (-x - Ein x), so q(1) is the limit of X e ^ -Ein X,
which is e ^ -γ since Ein X = log X + γ + o(1).
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bAdjoint8
import Mathlib.NumberTheory.Harmonic.GammaDeriv

open Real Filter Topology

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

theorem einB8_split_at_one {x : ℝ} (hx : 1 ≤ x) :
    einB8 x - log x = ∫ t in (0 : ℝ)..1, (1 - exp (-t)) / t - ∫ t in (1 : ℝ)..x, exp (-t) / t := by
  have h₁ : einB8 x = ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t := rfl
  rw [h₁]
  have h₂ : ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t = ∫ t in (0 : ℝ)..1, (1 - exp (-t)) / t + ∫ t in (1 : ℝ)..x, (1 - exp (-t)) / t := by
    rw [intervalIntegral.integral_add_integral (by norm_num : (0 : ℝ) ≤ 1) (by linarith)]
  rw [h₂]
  have h₃ : ∫ t in (1 : ℝ)..x, (1 - exp (-t)) / t = log x - ∫ t in (1 : ℝ)..x, exp (-t) / t := by
    have h₄ : ∫ t in (1 : ℝ)..x, (1 - exp (-t)) / t = ∫ t in (1 : ℝ)..x, ((1 : ℝ) / t - exp (-t) / t) := by
      apply intervalIntegral.integral_congr
      · intro t ht
        simp [ht]
      · intro t ht
        field_simp [ht.ne']
        <;> ring
    rw [h₄]
    have h₅ : ∫ t in (1 : ℝ)..x, ((1 : ℝ) / t - exp (-t) / t) = ∫ t in (1 : ℝ)..x, (1 / t : ℝ) - ∫ t in (1 : ℝ)..x, exp (-t) / t := by
      rw [intervalIntegral.integral_sub]
      · apply intervalIntegrable_iff_integrableOn_Icc.mpr
        constructor
        · exact ContinuousOn.div continuousOn_id continuousOn_const (by
            intro t ht
            have h₆ : 1 ≤ t := by exact ht.1
            linarith)
        · exact (continuousOn_id.measurableOnSet).measurable
      · apply intervalIntegrable_iff_integrableOn_Icc.mpr
        constructor
        · exact ContinuousOn.div (continuousOn_exp.neg.comp continuousOn_id) continuousOn_const (by
            intro t ht
            have h₆ : 1 ≤ t := by exact ht.1
            linarith)
        · exact (continuousOn_exp.neg.comp continuousOn_id).measurable
    rw [h₅]
    have h₆ : ∫ t in (1 : ℝ)..x, (1 / t : ℝ) = log x := by
      have h₇ : ∫ t in (1 : ℝ)..x, deriv (fun t : ℝ => Real.log t) t = Real.log x - Real.log 1 := by
        rw [intervalIntegral.integral_deriv (by
          intro t ht
          exact ContinuousAt.log (continuousAt_id t) (by linarith)
        )]
      have h₈ : ∫ t in (1 : ℝ)..x, deriv (fun t : ℝ => Real.log t) t = ∫ t in (1 : ℝ)..x, (1 / t : ℝ) := by
        apply intervalIntegral.integral_congr
        · intro t ht
          simp [ht]
        · intro t ht
          rw [deriv_log (by linarith)]
      rw [h₈] at h₇
      have h₉ : Real.log 1 = (0 : ℝ) := by norm_num
      rw [h₉] at h₇
      linarith
    rw [h₆]
    <;> ring_nf
  rw [h₃]
  <;> ring_nf

/-- LEAF: Nathanson Theorem 9.4, adjoint pairing evaluated at s = 3 and s = 1: with
p(t) = 0 on (0, 1), 1 / t on [1, 2] and (1 + log (t - 1)) / t on [2, 3], s p(s) is
continuous at 2 and satisfies (s p(s))' = p(s - 1) on (1, 3), so by leafB8_adjQ_deriv
s q'(s) = - q(s + 1) the pairing s p(s) q(s) + the integral of p(t) q(t + 1) over
[s - 1, s] has zero derivative on (1, 2) and (2, 3); its value at 3 is kConstB8 q and its
limit at 1 from the right is q(1). Class MEDIUM: FTC for parameter integrals and
continuity of q on [1, 4]. -/
theorem leafB8_adjQK_pairing : kConstB8 adjQB8 = adjQB8 1 := by
  sorry

/-- LEAF: Ein x = log x + γ + E_1(x) with E_1(x) → 0, so Ein x - log x → γ as x → ∞,
Abramowitz and Stegun 5.1.39. Class HARD: needs the integral representation of the
Euler Mascheroni constant, γ = the integral over [0, 1] of (1 - e ^ -t) / t minus the
integral over [1, ∞) of e ^ -t / t. -/
theorem leafB8_ein_asymp :
    Tendsto (fun x => einB8 x - log x) atTop (𝓝 eulerMascheroniConstant) := by
  sorry

/-- LEAF: g(x) = x e ^ -Ein x is continuous at 0 from the right and, for x > 0,
g'(x) = e ^ -Ein x - x Ein'(x) e ^ -Ein x = e ^ (-x - Ein x) since
Ein'(x) = (1 - e ^ -x) / x by FTC, the integrand extending continuously to 0.
Class MEDIUM: FTC for einB8 plus continuity of the integrand. -/
theorem leafB8_ein_deriv :
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

/-- q(1) = e ^ -γ, proved from leafB8_ein_deriv and leafB8_ein_asymp by the improper FTC. -/
theorem adjQB8_one : adjQB8 1 = exp (-eulerMascheroniConstant) := by
  obtain ⟨hc, hd⟩ := leafB8_ein_deriv
  have hlim : Tendsto (fun x => x * exp (-einB8 x)) atTop
      (𝓝 (exp (-eulerMascheroniConstant))) := by
    have h1 : Tendsto (fun x => exp (-(einB8 x - log x))) atTop
        (𝓝 (exp (-eulerMascheroniConstant))) :=
      (continuous_exp.tendsto _).comp leafB8_ein_asymp.neg
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_sub, exp_sub, exp_log hx, exp_neg, div_eq_mul_inv]
  have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hc hd
    (fun x _ => (exp_pos _).le) hlim
  unfold adjQB8
  rw [this]
  simp

/-- Twin of leafB8_adjQ_K, statement verbatim, proved from the three LEAFs above. -/
theorem leafB8_adjQ_K_twin : kConstB8 adjQB8 = exp (-eulerMascheroniConstant) := by
  rw [leafB8_adjQK_pairing, adjQB8_one]

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_adjQ_K_twin

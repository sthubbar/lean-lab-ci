/-
Proof of the LEAF leafB8_adjQ_tendsto of Split1122bAdjoint8.lean: the normalization
s q(s) → 1 as s → ∞ of the adjoint function of Nathanson Theorem 9.4, as quoted by
Bordignon, Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6.
Route: the squeeze exp (- x) ≤ exp (- Ein x) ≤ 1 for x ≥ 0, from 0 ≤ Ein x ≤ x, gives
1 / (s + 1) ≤ q(s) ≤ 1 / s for s > 0.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bAdjoint8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- The integrand of Ein, bounds on [0, ∞). -/
theorem einB8_integrand_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (1 - exp (-t)) / t ∧ (1 - exp (-t)) / t ≤ 1 := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp
  · refine ⟨div_nonneg (by linarith [exp_le_one_iff.2 (neg_nonpos.2 ht)]) h.le, ?_⟩
    rw [div_le_one h]
    linarith [add_one_le_exp (-t)]

theorem einB8_integrand_measurable :
    Measurable (fun t : ℝ => (1 - exp (-t)) / t) := by
  fun_prop

theorem einB8_integrableOn (b : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (1 - exp (-t)) / t) (Set.Icc 0 b) := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
    einB8_integrand_measurable.aestronglyMeasurable ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall ?_)
  intro t ht
  have := einB8_integrand_bounds ht.1
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

theorem einB8_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ einB8 x := by
  unfold einB8
  exact intervalIntegral.integral_nonneg hx (fun t ht => (einB8_integrand_bounds ht.1).1)

theorem einB8_le {x : ℝ} (hx : 0 ≤ x) : einB8 x ≤ x := by
  unfold einB8
  have hi : IntervalIntegrable (fun t : ℝ => (1 - exp (-t)) / t) MeasureTheory.volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2 (einB8_integrableOn x)
  calc (∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t) ≤ ∫ t in (0 : ℝ)..x, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hx hi intervalIntegrable_const
          (fun t ht => (einB8_integrand_bounds ht.1).2)
    _ = x := by simp

theorem einB8_continuousOn : ContinuousOn einB8 (Set.Ioi 0) := by
  intro x hx
  have hc : ContinuousOn einB8 (Set.Icc 0 (x + 1)) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := x + 1)
      (μ := MeasureTheory.volume) (f := fun t : ℝ => (1 - exp (-t)) / t)
      (by rw [Set.uIcc_of_le (by linarith [(Set.mem_Ioi.1 hx)])]; exact einB8_integrableOn _)
    rwa [Set.uIcc_of_le (by linarith [(Set.mem_Ioi.1 hx)])] at this
  exact (hc.continuousAt (Icc_mem_nhds (Set.mem_Ioi.1 hx) (by linarith))).continuousWithinAt

theorem adjQB8_bounds {s : ℝ} (hs : 0 < s) :
    1 / (s + 1) ≤ adjQB8 s ∧ adjQB8 s ≤ 1 / s := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun x => exp (-s * x - einB8 x))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (((continuous_const.mul continuous_id).continuousOn).sub einB8_continuousOn).rexp
  have hup : MeasureTheory.IntegrableOn (fun x : ℝ => exp (-s * x)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hs
  have hlo : MeasureTheory.IntegrableOn (fun x : ℝ => exp (-(s + 1) * x)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  have hle : ∀ x ∈ Set.Ioi (0 : ℝ), exp (-s * x - einB8 x) ≤ exp (-s * x) := fun x hx =>
    exp_le_exp.2 (by linarith [einB8_nonneg (le_of_lt hx)])
  have hge : ∀ x ∈ Set.Ioi (0 : ℝ), exp (-(s + 1) * x) ≤ exp (-s * x - einB8 x) := fun x hx =>
    exp_le_exp.2 (by nlinarith [einB8_le (le_of_lt hx)])
  have hint : MeasureTheory.IntegrableOn (fun x => exp (-s * x - einB8 x)) (Set.Ioi 0) := by
    refine hup.mono' hmeas ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall ?_)
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hle x hx
  have e1 : ∫ x in Set.Ioi (0 : ℝ), exp (-s * x) = 1 / s := by
    rw [integral_exp_mul_Ioi (by linarith) 0]; field_simp; simp
  have e2 : ∫ x in Set.Ioi (0 : ℝ), exp (-(s + 1) * x) = 1 / (s + 1) := by
    rw [integral_exp_mul_Ioi (by linarith) 0]
    have : s + 1 ≠ 0 := by linarith
    field_simp; simp
  constructor
  · rw [← e2]; unfold adjQB8
    exact MeasureTheory.setIntegral_mono_on hlo hint measurableSet_Ioi hge
  · rw [← e1]; unfold adjQB8
    exact MeasureTheory.setIntegral_mono_on hint hup measurableSet_Ioi hle

/-- Twin of leafB8_adjQ_tendsto of Split1122bAdjoint8.lean, statement copied verbatim. -/
theorem leafB8_adjQ_tendsto_twin :
    Filter.Tendsto (fun s => s * adjQB8 s) Filter.atTop (nhds 1) := by
  have hlow : Filter.Tendsto (fun s : ℝ => 1 - 1 / (s + 1)) Filter.atTop (nhds 1) := by
    have : Filter.Tendsto (fun s : ℝ => 1 / (s + 1)) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right _ (1 : ℝ) Filter.tendsto_id)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    have h := (adjQB8_bounds hs).1
    have : 1 - 1 / (s + 1) = s * (1 / (s + 1)) := by field_simp; ring
    rw [this]; exact mul_le_mul_of_nonneg_left h hs.le
  · filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    have h := mul_le_mul_of_nonneg_left (adjQB8_bounds hs).2 hs.le
    rwa [mul_one_div_cancel hs.ne'] at h

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_adjQ_tendsto_twin

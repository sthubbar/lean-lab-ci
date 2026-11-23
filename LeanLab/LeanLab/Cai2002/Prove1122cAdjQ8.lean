/-
Proofs of the two remaining LEAFs of Split1122bAdjoint8.lean, the adjoint function of
Nathanson Theorem 9.4 as quoted by Bordignon, Johnston and Starichkova, arXiv 2207.09452v6,
papers/P0009.pdf, page 6:
* leafB8_adjQ_deriv, s q'(s) = - q(s + 1) for s > 0, as Deriv1122c.leafB8_adjQ_deriv_1122c;
* leafB8_adjQ_tendsto, s q(s) → 1, as Tend1122c.leafB8_adjQ_tendsto_1122c.
With Prove1122cEin8.lean and Prove1122cAdjQKPair8.lean this proves leafB8_adjoint of
Split1122bBoundary8.lean with no LEAF, as leafB8_adjoint_proved1122c.
Helpers of each proof live in their own namespace; several are copies of the helpers of
Prove1122cEin8.lean.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122cAdjQKPair8

namespace LeanLab.Cai2002

namespace Deriv1122c
open Real Filter Topology
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


lemma ein_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ einB8 x :=
  intervalIntegral.integral_nonneg hx (fun t ht => (f_bounds ht.1).1)

lemma ein_contOn : ContinuousOn einB8 (Ioi 0) := fun x hx =>
  (ein_hasDerivAt hx).continuousAt.continuousWithinAt

lemma ein_cwa0 : ContinuousWithinAt einB8 (Ici 0) 0 := by
  have habs : Tendsto (fun e : ℝ => |e|) (𝓝[≥] 0) (𝓝 0) := by
    have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ici 0))
    simpa using this
  have h0 : einB8 0 = 0 := by simp [einB8]
  rw [ContinuousWithinAt, h0]
  refine squeeze_zero_norm' ?_ habs
  filter_upwards [self_mem_nhdsWithin] with e (he : 0 ≤ e)
  rw [Real.norm_eq_abs, abs_of_nonneg he]; exact ein_abs_le he

lemma integrand_contOn (b : ℝ) :
    ContinuousOn (fun x => exp (-b * x - einB8 x)) (Ioi 0) :=
  Real.continuous_exp.comp_continuousOn
    ((by fun_prop : Continuous fun x : ℝ => -b * x).continuousOn.sub ein_contOn)

lemma exp_bound {b x : ℝ} (hx : 0 ≤ x) : exp (-b * x - einB8 x) ≤ exp (-b * x) :=
  exp_le_exp.mpr (by linarith [ein_nonneg hx])

lemma intA {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x => exp (-b * x - einB8 x)) (Ioi 0) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hb)
    ((integrand_contOn b).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_bound (le_of_lt hx)

lemma xexp_int {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x * exp (-b * x)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) one_pos hb
  refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

lemma intB {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x => x * exp (-b * x - einB8 x)) (Ioi 0) := by
  refine Integrable.mono' (xexp_int hb)
    ((continuousOn_id.mul (integrand_contOn b)).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx' : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hx' (exp_pos _))]
  exact mul_le_mul_of_nonneg_left (exp_bound hx'.le) hx'.le

lemma ibp {s : ℝ} (hs : 0 < s) :
    adjQB8 (s + 1) = s * ∫ x in Ioi (0 : ℝ), x * exp (-s * x - einB8 x) := by
  set u : ℝ → ℝ := fun x => x * exp (-s * x - einB8 x) with hu
  have hcont : ContinuousWithinAt u (Ici 0) 0 := by
    have : ContinuousWithinAt (fun x : ℝ => -s * x - einB8 x) (Ici 0) 0 :=
      ((by fun_prop : Continuous fun x : ℝ => -s * x).continuousWithinAt).sub ein_cwa0
    exact continuousWithinAt_id.mul (Real.continuous_exp.continuousAt.comp_continuousWithinAt this)
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u
      (exp (-(s + 1) * x - einB8 x) - s * (x * exp (-s * x - einB8 x))) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h1 : HasDerivAt (fun x : ℝ => -s * x - einB8 x) (-s * 1 - (1 - exp (-x)) / x) x :=
      ((hasDerivAt_id' x).const_mul (-s)).sub (ein_hasDerivAt hx')
    have h : HasDerivAt u
        (1 * exp (-s * x - einB8 x) + x * (exp (-s * x - einB8 x) * (-s * 1 - (1 - exp (-x)) / x))) x :=
      (hasDerivAt_id' x).mul h1.exp
    refine h.congr_deriv ?_
    rw [show -(s + 1) * x - einB8 x = -x + (-s * x - einB8 x) by ring, Real.exp_add]
    field_simp
    ring
  have hint : IntegrableOn
      (fun x => exp (-(s + 1) * x - einB8 x) - s * (x * exp (-s * x - einB8 x))) (Ioi 0) :=
    (intA (by linarith)).sub ((intB hs).const_mul s)
  have hlim : Tendsto u atTop (𝓝 0) := by
    have hg : Tendsto (fun x : ℝ => (s * x) ^ 1 * exp (-(s * x)) / s) atTop (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop hs)).div_const s
      simpa using this
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.norm_eq_abs, hu, abs_of_nonneg (mul_nonneg hx (exp_pos _).le)]
    calc x * exp (-s * x - einB8 x) ≤ x * exp (-s * x) :=
          mul_le_mul_of_nonneg_left (exp_bound hx) hx
      _ = (s * x) ^ 1 * exp (-(s * x)) / s := by
          rw [show -(s * x) = -s * x by ring]; field_simp
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [integral_sub (intA (by linarith)) ((intB hs).const_mul s), integral_const_mul] at key
  simp only [hu, zero_mul, sub_zero] at key
  unfold adjQB8
  linarith

/-- Proof of the LEAF leafB8_adjQ_deriv of Split1122bAdjoint8.lean, statement verbatim:
Nathanson Theorem 9.4 delay relation s q'(s) = - q(s + 1), by dominated differentiation
under the integral and integration by parts on (0, ∞). -/
theorem leafB8_adjQ_deriv_1122c (s : ℝ) (hs : 0 < s) : HasDerivAt adjQB8 (-adjQB8 (s + 1) / s) s := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (t : ℝ) (x : ℝ) => exp (-t * x - einB8 x))
    (F' := fun (t : ℝ) (x : ℝ) => exp (-t * x - einB8 x) * (-x))
    (bound := fun x => x * exp (-(s / 2) * x))
    (x₀ := s) (s := Ioi (s / 2))
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun t => (integrand_contOn t).aestronglyMeasurable measurableSet_Ioi)
    (intA hs)
    (((integrand_contOn s).mul continuousOn_id.neg).aestronglyMeasurable measurableSet_Ioi)
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx t ht => ?_)
      have hx' : (0 : ℝ) < x := hx
      have ht' : s / 2 < t := ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), abs_neg, abs_of_pos hx', mul_comm]
      refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) hx'.le
      have : s / 2 * x ≤ t * x := mul_le_mul_of_nonneg_right ht'.le hx'.le
      linarith [ein_nonneg hx'.le])
    (xexp_int hs2)
    (by
      refine Eventually.of_forall fun x t _ => ?_
      have h : HasDerivAt (fun t : ℝ => -t * x - einB8 x) (-1 * x) t := by
        simpa using (((hasDerivAt_id' t).neg).mul_const x).sub_const (einB8 x)
      simpa using h.exp)
  have hfun : (fun t => ∫ x, exp (-t * x - einB8 x) ∂(volume.restrict (Ioi (0 : ℝ)))) = adjQB8 :=
    rfl
  rw [hfun] at hD
  refine hD.2.congr_deriv ?_
  have h1 : ∫ x in Ioi (0 : ℝ), exp (-s * x - einB8 x) * (-x)
      = -∫ x in Ioi (0 : ℝ), x * exp (-s * x - einB8 x) := by
    rw [← integral_neg]; congr 1; ext x; ring
  rw [h1, ibp hs, neg_div, mul_div_cancel_left₀ _ hs.ne']

end Deriv1122c

namespace Tend1122c
open Real Filter Topology
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



lemma ein_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ einB8 x := by
  unfold einB8
  exact intervalIntegral.integral_nonneg hx (fun t ht => (f_bounds ht.1).1)

lemma ein_contOn : ContinuousOn einB8 (Ioi 0) := fun x hx =>
  (ein_hasDerivAt hx).continuousAt.continuousWithinAt

lemma s_adj_eq {s : ℝ} (hs : 0 < s) :
    s * adjQB8 s = ∫ y in Ioi (0 : ℝ), exp (-y - einB8 (y / s)) := by
  have := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y => exp (-y - einB8 (y / s))) 0 hs
  simp only [mul_zero, smul_eq_mul] at this
  have h2 : (fun x : ℝ => exp (-(s * x) - einB8 (s * x / s))) = fun x => exp (-s * x - einB8 x) := by
    funext x; rw [mul_div_cancel_left₀ x hs.ne']; ring_nf
  rw [h2] at this
  unfold adjQB8; rw [this, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

theorem leafB8_adj_tendsto : Filter.Tendsto (fun s => s * adjQB8 s) Filter.atTop (nhds 1) := by
  have hint : IntegrableOn (fun y : ℝ => exp (-y)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 zero_lt_one
  have hlim : Tendsto (fun s => ∫ y in Ioi (0 : ℝ), exp (-y - einB8 (y / s))) atTop
      (𝓝 (∫ y in Ioi (0 : ℝ), exp (-y))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun y => exp (-y)) ?_ ?_ hint ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.rexp (ContinuousOn.sub (continuous_neg.continuousOn) ?_)
      exact ein_contOn.comp (continuous_id.div_const s).continuousOn
        (fun y (hy : 0 < y) => div_pos hy hs)
    · filter_upwards [eventually_gt_atTop 0] with s hs
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y (hy : 0 < y) => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr (by linarith [ein_nonneg (div_pos hy hs).le])
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y (hy : 0 < y) => ?_)
      have hE : Tendsto (fun s => einB8 (y / s)) atTop (𝓝 0) := by
        have hd : Tendsto (fun s => y / s) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
        refine squeeze_zero_norm' ?_ hd
        filter_upwards [eventually_gt_atTop 0] with s hs
        have hp := div_pos hy hs
        rw [Real.norm_eq_abs]
        exact ein_abs_le hp.le
      have := (tendsto_const_nhds (x := -y)).sub hE
      rw [sub_zero] at this
      exact (Real.continuous_exp.tendsto _).comp this
  rw [integral_exp_neg_Ioi_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  exact (s_adj_eq hs).symm

/-- Proof of the LEAF leafB8_adjQ_tendsto of Split1122bAdjoint8.lean, statement verbatim:
s q(s) → 1, by x = y / s and dominated convergence with bound e ^ -y. -/
theorem leafB8_adjQ_tendsto_1122c : Filter.Tendsto (fun s => s * adjQB8 s) Filter.atTop (nhds 1) :=
  leafB8_adj_tendsto

end Tend1122c

/-- Twin of leafB8_adjQ_K of Split1122bAdjoint8.lean, statement verbatim, with no LEAF:
K(q) = e ^ -γ for the explicit adjoint function. -/
theorem leafB8_adjQ_K_proved1122c :
    kConstB8 adjQB8 = Real.exp (-Real.eulerMascheroniConstant) := by
  rw [adjQK_pairing_of_deriv1122c adjQB8 Deriv1122c.leafB8_adjQ_deriv_1122c, adjQB8_one_1122c]

/-- Twin of leafB8_adjoint of Split1122bBoundary8.lean, statement verbatim, with no LEAF:
Nathanson Theorem 9.4, an adjoint function q with s q'(s) = - q(s + 1), s q(s) → 1 and
K(q) = e ^ -γ exists. -/
theorem leafB8_adjoint_proved1122c :
    ∃ q : ℝ → ℝ, IsAdjB8 q ∧ kConstB8 q = Real.exp (-Real.eulerMascheroniConstant) :=
  ⟨adjQB8, ⟨fun s hs => Deriv1122c.leafB8_adjQ_deriv_1122c s hs,
    Tend1122c.leafB8_adjQ_tendsto_1122c⟩, leafB8_adjQ_K_proved1122c⟩

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.Deriv1122c.leafB8_adjQ_deriv_1122c
#print axioms LeanLab.Cai2002.Tend1122c.leafB8_adjQ_tendsto_1122c
#print axioms LeanLab.Cai2002.leafB8_adjQ_K_proved1122c
#print axioms LeanLab.Cai2002.leafB8_adjoint_proved1122c

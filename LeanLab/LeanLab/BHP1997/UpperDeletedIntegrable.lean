/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 53. Integrability of the conservative
deleted integrand.

Unit P1122-0084, QUESTION 3 of the upslack line in PROGRESS.md. `upperDeletedIntegral` is a
totalized iterated Bochner interval integral. This file shows that under the hypotheses of
`upper_deleted_integral_bound` the integrand is jointly measurable and bounded by 5000, so it
is integrable on the product box, every inner integral is interval integrable, and the lab
value equals the genuine integral over the product box by Fubini. So the totalization never
fires and the lab value is the true integral.

Goldbach is open. AI wrote this Lean code.
-/
import LeanLab.BHP1997.DecompC165dBase312

namespace LeanLab.BHP1997.DecompC165d
open Classical MeasureTheory

/-- The box side `Ioc (upperGridReal 0) (upperGridReal 64)`. -/
noncomputable def upperBoxSide : Set ℝ := Set.Ioc (upperGridReal 0) (upperGridReal 64)

theorem upper_grid_box_le : upperGridReal 0 ≤ upperGridReal 64 := by
  unfold upperGridReal upperGridPoint
  gcongr <;> norm_num

/-- Page 53. The support condition of the deleted integrand is a measurable subset of space,
as a boolean combination of closed half spaces. -/
theorem upper_deleted_region_measurable (ε : ℝ) :
    Measurable (fun p : ℝ × ℝ × ℝ =>
      (1+7*(2*(1/16-1/10^5)))/15-ε ≤ p.2.2 ∧ p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ p.1 ∧
        p.1 ≤ 1/4+(2*(1/16-1/10^5))/8-ε ∧ ¬upperPrimeCovered ε p.1 p.2.1 p.2.2) := by
  have hle : ∀ f g : ℝ × ℝ × ℝ → ℝ, Continuous f → Continuous g →
      Measurable (fun p => f p ≤ g p) := fun f g hf hg =>
    measurableSet_setOf.mp (isClosed_le hf hg).measurableSet
  unfold upperPrimeCovered upperPairRegion
  repeat' first
    | apply Measurable.and
    | apply Measurable.or
    | apply Measurable.not
    | (apply hle <;> fun_prop)

/-- Page 53. The deleted integrand, uncurried on three space, is measurable. -/
theorem upper_deleted_integrand_measurable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) (ε : ℝ) :
    Measurable (fun p : ℝ × ℝ × ℝ => upperDeletedIntegrand ω ε p.1 p.2.1 p.2.2) := by
  have hm : Measurable ω := by
    have h : ω = (Set.Ici (1:ℝ)).piecewise ω (fun _ => 0) := by
      funext u
      by_cases hu : u ∈ Set.Ici (1:ℝ)
      · rw [Set.piecewise_eq_of_mem _ _ _ hu]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hu]
        exact hz u (not_le.1 hu)
    rw [h]
    exact hω.1.measurable_piecewise continuousOn_const measurableSet_Ici
  unfold upperDeletedIntegrand
  refine Measurable.ite (measurableSet_setOf.mpr (upper_deleted_region_measurable ε)) ?_
    measurable_const
  refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const ?_
  fun_prop

/-- Page 53. The deleted integrand lies between 0 and 5000 everywhere. -/
theorem upper_deleted_integrand_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) (a b c : ℝ) :
    0 ≤ upperDeletedIntegrand ω ε a b c ∧ upperDeletedIntegrand ω ε a b c ≤ 5000 := by
  refine ⟨upper_deleted_nonneg hω hε hε' a b c, ?_⟩
  unfold upperDeletedIntegrand
  split_ifs with hdom hu
  · norm_num
  · obtain ⟨hcc, hcb, hba, _, _⟩ := hdom
    have hp := upper_grid_parameters hε hε'
    have hc0' : (49996:ℝ)/400000 ≤ c := le_trans hp.1.le hcc
    set g : ℝ := 49996/400000 with hg
    have hc0 : g ≤ c := hc0'
    have hb0 : g ≤ b := hc0.trans hcb
    have ha0 : g ≤ a := hb0.trans hba
    have hgpos : 0 < g := by rw [hg]; norm_num
    have hd : g^4 ≤ a*b*c^2 := by
      have : g^4 = g*g*g^2 := by ring
      rw [this]
      gcongr
    have hdpos : 0 < a*b*c^2 := lt_of_lt_of_le (by positivity) hd
    have h1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz
      ((1-a-b-c)/c)
    calc ω ((1-a-b-c)/c)/(a*b*c^2) ≤ 1/(a*b*c^2) :=
          div_le_div_of_nonneg_right h1 hdpos.le
      _ ≤ 1/g^4 := div_le_div_of_nonneg_left zero_le_one (by positivity) hd
      _ ≤ 5000 := by rw [hg]; norm_num
  · norm_num

/-- Page 53. The uncurried deleted integrand is integrable on the product box. -/
theorem upper_deleted_integrableOn_box {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    IntegrableOn (fun p : ℝ × ℝ × ℝ => upperDeletedIntegrand ω ε p.1 p.2.1 p.2.2)
      (upperBoxSide ×ˢ (upperBoxSide ×ˢ upperBoxSide)) := by
  have hfin : volume (upperBoxSide ×ˢ (upperBoxSide ×ˢ upperBoxSide)) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    unfold upperBoxSide
    simp [Real.volume_Ioc, ENNReal.mul_eq_top]
  refine Measure.integrableOn_of_bounded (M := 5000) hfin
    (upper_deleted_integrand_measurable hω hz ε).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  have h := upper_deleted_integrand_bound hω hz hε hε' p.1 p.2.1 p.2.2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Page 53. For fixed `a` the integrand in `(b, c)` is integrable on the square. -/
theorem upper_deleted_integrableOn_square {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) (a : ℝ) :
    IntegrableOn (fun q : ℝ × ℝ => upperDeletedIntegrand ω ε a q.1 q.2)
      (upperBoxSide ×ˢ upperBoxSide) := by
  have hfin : volume (upperBoxSide ×ˢ upperBoxSide) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    unfold upperBoxSide
    simp [Real.volume_Ioc, ENNReal.mul_eq_top]
  have hm : Measurable (fun q : ℝ × ℝ => upperDeletedIntegrand ω ε a q.1 q.2) :=
    (upper_deleted_integrand_measurable hω hz ε).comp (measurable_prodMk_left (x := a))
  refine Measure.integrableOn_of_bounded (M := 5000) hfin hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  have h := upper_deleted_integrand_bound hω hz hε hε' a q.1 q.2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Page 53. The innermost `c` integrand is interval integrable for all `a` and `b`. -/
theorem upper_deleted_inner_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) (a b : ℝ) :
    IntervalIntegrable (fun c => upperDeletedIntegrand ω ε a b c) volume
      (upperGridReal 0) (upperGridReal 64) := by
  have hm : Measurable (fun c : ℝ => upperDeletedIntegrand ω ε a b c) :=
    (upper_deleted_integrand_measurable hω hz ε).comp
      ((measurable_prodMk_left (x := a)).comp (measurable_prodMk_left (x := b)))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le upper_grid_box_le]
  refine Measure.integrableOn_of_bounded (M := 5000) measure_Ioc_lt_top.ne
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun c => ?_)
  have h := upper_deleted_integrand_bound hω hz hε hε' a b c
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Page 53. The middle `b` integrand, an integral over `c`, is interval integrable
for every `a`. -/
theorem upper_deleted_middle_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) (a : ℝ) :
    IntervalIntegrable
      (fun b => ∫ c in upperGridReal 0..upperGridReal 64, upperDeletedIntegrand ω ε a b c)
      volume (upperGridReal 0) (upperGridReal 64) := by
  have hG : (fun b => ∫ c in upperGridReal 0..upperGridReal 64,
        upperDeletedIntegrand ω ε a b c) =
      fun b => ∫ c in upperBoxSide, upperDeletedIntegrand ω ε a b c :=
    funext fun b => intervalIntegral.integral_of_le upper_grid_box_le
  have hm2 : Measurable (fun q : ℝ × ℝ => upperDeletedIntegrand ω ε a q.1 q.2) :=
    (upper_deleted_integrand_measurable hω hz ε).comp (measurable_prodMk_left (x := a))
  have hm : StronglyMeasurable
      (fun b => ∫ c in upperBoxSide, upperDeletedIntegrand ω ε a b c) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict upperBoxSide)
      (f := fun q : ℝ × ℝ => upperDeletedIntegrand ω ε a q.1 q.2) hm2.stronglyMeasurable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le upper_grid_box_le, hG]
  refine Measure.integrableOn_of_bounded
    (M := 5000 * |upperGridReal 64 - upperGridReal 0|) measure_Ioc_lt_top.ne
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
  unfold upperBoxSide
  rw [← intervalIntegral.integral_of_le upper_grid_box_le]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun c _ => ?_
  have h := upper_deleted_integrand_bound hω hz hε hε' a b c
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Page 53. The outer `a` integrand, the double integral over `b` and `c`, is interval
integrable. With the two lemmas above, every integral in `upperDeletedIntegral` is a
genuine integral of an integrable function. -/
theorem upper_deleted_outer_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    IntervalIntegrable
      (fun a => ∫ b in upperGridReal 0..upperGridReal 64,
        ∫ c in upperGridReal 0..upperGridReal 64, upperDeletedIntegrand ω ε a b c)
      volume (upperGridReal 0) (upperGridReal 64) := by
  have hG : (fun a => ∫ b in upperGridReal 0..upperGridReal 64,
        ∫ c in upperGridReal 0..upperGridReal 64, upperDeletedIntegrand ω ε a b c) =
      fun a => ∫ b in upperBoxSide, ∫ c in upperBoxSide, upperDeletedIntegrand ω ε a b c := by
    funext a
    rw [intervalIntegral.integral_of_le upper_grid_box_le]
    refine setIntegral_congr_fun measurableSet_Ioc fun b _ => ?_
    exact intervalIntegral.integral_of_le upper_grid_box_le
  have hm3 := upper_deleted_integrand_measurable hω hz ε
  have hm2 : StronglyMeasurable
      (fun ab : ℝ × ℝ => ∫ c in upperBoxSide, upperDeletedIntegrand ω ε ab.1 ab.2 c) := by
    have hm3' : Measurable
        (fun q : (ℝ × ℝ) × ℝ => upperDeletedIntegrand ω ε q.1.1 q.1.2 q.2) :=
      hm3.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, (q.1.2, q.2))) (by fun_prop)
    exact StronglyMeasurable.integral_prod_right' (ν := volume.restrict upperBoxSide)
      (f := fun q : (ℝ × ℝ) × ℝ => upperDeletedIntegrand ω ε q.1.1 q.1.2 q.2)
      hm3'.stronglyMeasurable
  have hm : StronglyMeasurable
      (fun a => ∫ b in upperBoxSide, ∫ c in upperBoxSide, upperDeletedIntegrand ω ε a b c) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict upperBoxSide)
      (f := fun ab : ℝ × ℝ => ∫ c in upperBoxSide, upperDeletedIntegrand ω ε ab.1 ab.2 c) hm2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le upper_grid_box_le, hG]
  refine Measure.integrableOn_of_bounded
    (M := 5000 * |upperGridReal 64 - upperGridReal 0| * |upperGridReal 64 - upperGridReal 0|)
    measure_Ioc_lt_top.ne hm.aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
  unfold upperBoxSide
  simp_rw [← intervalIntegral.integral_of_le upper_grid_box_le]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun b _ => ?_
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun c _ => ?_
  have h := upper_deleted_integrand_bound hω hz hε hε' a b c
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- Page 53. Fubini: the lab's iterated `upperDeletedIntegral` equals the integral of the
uncurried integrand over the product box. So the lab value is the true integral, not an
artifact of the totalized Bochner convention. -/
theorem upper_deleted_integral_eq_box {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    upperDeletedIntegral ω ε =
      ∫ p in upperBoxSide ×ˢ (upperBoxSide ×ˢ upperBoxSide),
        upperDeletedIntegrand ω ε p.1 p.2.1 p.2.2 := by
  have h3 := upper_deleted_integrableOn_box hω hz hε hε'
  rw [Measure.volume_eq_prod] at h3 ⊢
  rw [setIntegral_prod _ h3]
  unfold upperDeletedIntegral
  rw [intervalIntegral.integral_of_le upper_grid_box_le]
  refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
  have h2 := upper_deleted_integrableOn_square hω hz hε hε' a
  rw [Measure.volume_eq_prod] at h2
  simp only
  rw [Measure.volume_eq_prod, setIntegral_prod _ h2,
    intervalIntegral.integral_of_le upper_grid_box_le]
  refine setIntegral_congr_fun measurableSet_Ioc fun b _ => ?_
  exact intervalIntegral.integral_of_le upper_grid_box_le

end LeanLab.BHP1997.DecompC165d

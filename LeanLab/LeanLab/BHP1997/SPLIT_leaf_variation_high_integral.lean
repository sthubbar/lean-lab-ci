/-
The split of `leaf_variation_high_integral` of `SPLIT_leaf_two_variation_quadrature`.

`two_variation_bound` bounds the majorant of the discarded lower coefficient integrand by three
branches selected by `a + 3 b`. The leaf handled here is the branch taken when `1 ≤ a + 3 b`,
integrated over the box `a, b ∈ [1/10, 1/2]`, with bound `3/2`. A quadrature of that branch gives
about 1.4923, so the bound has almost no room and no relaxation of the discarded set is
affordable. The split therefore leaves the discarded set exactly as it is and cuts only the outer
`a`-integral:

* `leaf_high_vanishing_strip`: for `a ≤ 24999/100000` the integrand vanishes identically on the
  strip, because the discarded set gives `b ≤ a`, hence `1 ≤ a + 3 b ≤ a + 3 a = 4 a < 1`;
* `leaf_high_strip_one`, `leaf_high_strip_two`, `leaf_high_strip_three`, `leaf_high_strip_four`:
  the four strips of `a` between `24999/100000` and `1/2`, bounded by the quadrature values
  `0.1784`, `0.4656`, `0.4719` and `0.3839`, which add up to `1.4998`.

The assembly adds the five strips with the additivity of the interval integral, which needs the
inner integral to be a bounded measurable function of `a`. The vanishing strip is proved here; the
four numerical strips are open leaves. No new definition.
-/
import LeanLab.BHP1997.SPLIT_leaf_two_variation_quadrature

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open MeasureTheory Set
open scoped BigOperators

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

/-- The high branch of the majorant of `two_variation_bound` is at most `10^4` everywhere: on the
discarded set this is `two_variation_bound`, off it the branch is zero. -/
private theorem hi_abs_bound {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a b : ℝ) :
    |(if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)| ≤ 10^4 := by
  have hb := two_variation_bound hε8 a b
  by_cases h1 : 1 ≤ a+3*b
  · rw [ite_eq_left h1] at hb ⊢
    rw [abs_le]
    exact ⟨by linarith [hb.1], hb.2⟩
  · rw [ite_eq_right h1]
    norm_num

/-- The high branch is a measurable function of the pair `(a, b)`. -/
private theorem hi_measurable (ε : ℝ) :
    Measurable (fun p : ℝ × ℝ => if 1 ≤ p.1 + 3*p.2 then
      (if lowerTwoDiscarded ε p.1 p.2 then
        1/(p.1*p.2*(99/100-p.1-p.2)*(1-p.1-p.2)) else 0) else 0) := by
  refine Measurable.ite ?_ (Measurable.ite (two_density_region_measurable ε) (by fun_prop)
    measurable_const) measurable_const
  exact measurableSet_le measurable_const (by fun_prop)

/-- A measurable function bounded by `M` is interval integrable. -/
private theorem hi_int_aux {f : ℝ → ℝ} {M : ℝ}
    (hm : Measurable f) (hM : ∀ x, ‖f x‖ ≤ M) (lo hi : ℝ) :
    IntervalIntegrable f volume lo hi := by
  refine ⟨Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_,
    Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_⟩
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact hM x
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact hM x

/-- The `b`-integral of the high branch is an interval-integrable function of `a` on every
interval, being measurable with absolute value at most `10^4 * (1/2 - 1/10)`. -/
private theorem hi_intO {ε : ℝ} (hε8 : ε ≤ 1/10^8) (x y : ℝ) :
    IntervalIntegrable (fun a : ℝ => (∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)))
      volume x y := by
  have h4 := four_density_level
    (fun (u : ℝ) (v : ℝ) => (if 1 ≤ u+3*v then
      (if lowerTwoDiscarded ε u v then 1/(u*v*(99/100-u-v)*(1-u-v)) else 0) else 0))
    (hi_measurable ε) (fun u v => hi_abs_bound hε8 u v) (1/10) (1/2)
  refine hi_int_aux (M := 4000) h4.1 (fun z => ?_) x y
  have hh := h4.2 z
  have h2 : (10^4:ℝ) * |(1/2:ℝ) - 1/10| = 4000 := by norm_num
  rw [Real.norm_eq_abs]
  exact hh.trans (le_of_eq h2)

/-- Below `a = 24999/100000` the integrand of the high branch vanishes identically in `b`: the
discarded set forces `b ≤ a`, so `1 ≤ a + 3 b ≤ 4 a < 1`. -/
private theorem hi_zero_slice {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ}
    (ha : a ≤ 24999/100000) :
    (∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) = 0 := by
  rw [show (∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if 1 ≤ a+3*b then
          (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      = ∫ b in (1/10:ℝ)..(1/2:ℝ), ((0:ℝ)) from
    intervalIntegral.integral_congr (fun b _ => by
      by_cases h1 : 1 ≤ a+3*b
      · by_cases hD : lowerTwoDiscarded ε a b
        · exfalso
          obtain ⟨-, hba, -, -⟩ := lower_two_domain_box hε8 hD
          linarith
        · rw [ite_eq_left h1, ite_eq_right hD]
      · rw [ite_eq_right h1])]
  exact intervalIntegral.integral_zero

/-- LEAF: the part of the high branch with `a ≤ 24999/100000` contributes nothing to the double
integral, because the discarded set forces `1 ≤ a + 3 b ≤ 4 a < 1` there. -/
theorem leaf_high_vanishing_strip {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(24999/100000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ 0 := by
  have hcongr : (∫ a in (1/10:ℝ)..(24999/100000:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
        (if 1 ≤ a+3*b then
          (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      = ∫ a in (1/10:ℝ)..(24999/100000:ℝ), ((0:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro a ha
    rw [Set.uIcc_of_le (by norm_num : (1/10:ℝ) ≤ 24999/100000)] at ha
    exact hi_zero_slice hε8 ha.2
  rw [hcongr, intervalIntegral.integral_zero]

/-- LEAF: the strip `24999/100000 ≤ a ≤ 5/16` of the high branch contributes at most `0.1784`;
the quadrature value of the strip is about `0.17654`. -/
theorem leaf_high_strip_one {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (24999/100000:ℝ)..(5/16:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      ≤ 223/1250 := by
  sorry

/-- LEAF: the strip `5/16 ≤ a ≤ 3/8` of the high branch contributes at most `0.4656`; the
quadrature value of the strip is about `0.46371`. -/
theorem leaf_high_strip_two {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (5/16:ℝ)..(3/8:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      ≤ 291/625 := by
  sorry

/-- LEAF: the strip `3/8 ≤ a ≤ 7/16` of the high branch contributes at most `0.4719`; the
quadrature value of the strip is about `0.47003`. -/
theorem leaf_high_strip_three {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (3/8:ℝ)..(7/16:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      ≤ 4719/10000 := by
  sorry

/-- LEAF: the strip `7/16 ≤ a ≤ 1/2` of the high branch contributes at most `0.3839`; the
quadrature value of the strip is about `0.38199`. -/
theorem leaf_high_strip_four {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (7/16:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0))
      ≤ 3839/10000 := by
  sorry

/-- The branch of the majorant taken when `1 ≤ a + 3 b`, integrated over the box, is at most
`3/2`: the five strips of the outer integral add up to at most `1.4998`. -/
theorem leaf_variation_high_integral_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ 3/2 := by
  have hI := hi_intO (ε := ε) hε8
  have e0 := intervalIntegral.integral_add_adjacent_intervals
    (hI (1/10) (24999/100000)) (hI (24999/100000) (1/2))
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (hI (24999/100000) (5/16)) (hI (5/16) (1/2))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (hI (5/16) (3/8)) (hI (3/8) (1/2))
  have e3 := intervalIntegral.integral_add_adjacent_intervals
    (hI (3/8) (7/16)) (hI (7/16) (1/2))
  have z := leaf_high_vanishing_strip hε hε8
  have s1 := leaf_high_strip_one hε hε8
  have s2 := leaf_high_strip_two hε hε8
  have s3 := leaf_high_strip_three hε hε8
  have s4 := leaf_high_strip_four hε hε8
  linarith [e0, e1, e2, e3, z, s1, s2, s3, s4]

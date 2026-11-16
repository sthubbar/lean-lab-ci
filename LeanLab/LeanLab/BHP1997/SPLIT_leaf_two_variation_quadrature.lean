/-
The split of `leaf_two_variation_quadrature` of `DensitySlope517`.

`two_variation_bound` bounds the majorant of the upward variation of the discarded lower
coefficient integrand by three branches selected by `a + 3 b`: at least one, at least `99/100`
and below one, and below `99/100`. The target integrates the sum of the three branches over the
box and asks for at most two. The split integrates one branch at a time:

* `leaf_variation_high_integral`: the branch with `1 ≤ a + 3 b`, at most `3/2`;
* `leaf_variation_middle_integral`: the branch with `99/100 ≤ a + 3 b < 1`, at most `1/10`;
* `leaf_variation_low_integral`: the branch with `a + 3 b < 99/100`, at most `2/5`.

A quadrature of the three pieces gives about 1.49, 0.06 and 0.14, and the three bounds add up
to two, so the leaves imply the target. Proved here: the pointwise identity of the integrand
with the sum of the three branches, the pointwise size of each branch, and the integrability
that lets the double integral of that sum split into three. No new definition.
-/
import LeanLab.BHP1997.DensitySlope517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open MeasureTheory Set
open scoped BigOperators

set_option maxHeartbeats 400000

/-- The first branch of the majorant of `two_variation_bound`, the one taken when
`1 ≤ a + 3 b`, lies between zero and `10^4`. -/
private theorem piece_high_bound {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a b : ℝ) :
    0 ≤ (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0) ∧
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0) ≤ 10^4 := by
  by_cases h1 : 1 ≤ a+3*b
  · have hb := two_variation_bound hε8 a b
    rw [ite_eq_left h1] at hb ⊢
    exact hb
  · rw [ite_eq_right h1]
    norm_num

/-- The second branch of the majorant of `two_variation_bound`, the one taken when
`99/100 ≤ a + 3 b < 1`, lies between zero and `10^4`. -/
private theorem piece_middle_bound {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a b : ℝ) :
    0 ≤ (if ¬(1 ≤ a+3*b) ∧ (99/100:ℝ) ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then (107/200)/(a*b^3) else 0) else 0) ∧
      (if ¬(1 ≤ a+3*b) ∧ (99/100:ℝ) ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then (107/200)/(a*b^3) else 0) else 0) ≤ 10^4 := by
  by_cases h1 : 1 ≤ a+3*b
  · rw [ite_eq_right (show ¬(¬(1 ≤ a+3*b) ∧ (99/100:ℝ) ≤ a+3*b) from fun h => h.1 h1)]
    norm_num
  · by_cases h2 : (99/100:ℝ) ≤ a+3*b
    · have hb := two_variation_bound hε8 a b
      rw [ite_eq_right h1] at hb
      rw [ite_eq_left h2] at hb
      rw [ite_eq_left (show ¬(1 ≤ a+3*b) ∧ (99/100:ℝ) ≤ a+3*b from ⟨h1, h2⟩)]
      exact hb
    · rw [ite_eq_right (show ¬(¬(1 ≤ a+3*b) ∧ (99/100:ℝ) ≤ a+3*b) from fun h => h2 h.2)]
      norm_num

/-- The third branch of the majorant of `two_variation_bound`, the one taken when
`a + 3 b < 99/100`, lies between zero and `10^4`. -/
private theorem piece_low_bound {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a b : ℝ) :
    0 ≤ (if a+3*b < (99/100:ℝ) then
        (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0) ∧
      (if a+3*b < (99/100:ℝ) then
        (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0) ≤ 10^4 := by
  by_cases h1 : 1 ≤ a+3*b
  · rw [ite_eq_right (by linarith : ¬ a+3*b < (99/100:ℝ))]
    norm_num
  · by_cases h2 : (99/100:ℝ) ≤ a+3*b
    · rw [ite_eq_right (by linarith : ¬ a+3*b < (99/100:ℝ))]
      norm_num
    · have hb := two_variation_bound hε8 a b
      rw [ite_eq_right h1] at hb
      rw [ite_eq_right h2] at hb
      rw [ite_eq_left (by linarith : a+3*b < (99/100:ℝ))]
      exact hb

/-- The integrand of the target is the sum of its three branches: exactly one of them is
nonzero at each point, and each branch carries the discarded set itself. -/
private theorem integrand_eq_pieces {ε : ℝ} (a b : ℝ) :
    (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0) =
      (if 1 ≤ a+3*b then
          (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)
      + (if ¬(1 ≤ a+3*b) ∧ (99/100:ℝ) ≤ a+3*b then
          (if lowerTwoDiscarded ε a b then (107/200)/(a*b^3) else 0) else 0)
      + (if a+3*b < (99/100:ℝ) then
          (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0) := by
  by_cases h1 : 1 ≤ a+3*b
  · have h3 : ¬ a+3*b < (99/100:ℝ) := by linarith
    by_cases hD : lowerTwoDiscarded ε a b <;> simp [hD, h1, h3]
  · by_cases h2 : (99/100:ℝ) ≤ a+3*b
    · have h3 : ¬ a+3*b < (99/100:ℝ) := by linarith
      by_cases hD : lowerTwoDiscarded ε a b <;> simp [hD, h1, h2, h3]
    · have h3 : a+3*b < (99/100:ℝ) := by linarith
      by_cases hD : lowerTwoDiscarded ε a b <;> simp [hD, h1, h2, h3]

/-- LEAF: the branch of the majorant taken when `1 ≤ a + 3 b`, integrated over the box, is at
most `3/2`. A quadrature gives about 1.49. -/
theorem leaf_variation_high_integral {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if 1 ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0)) ≤ 3/2 := by
  sorry

/-- LEAF: the branch of the majorant taken when `99/100 ≤ a + 3 b < 1`, integrated over the
box, is at most `1/10`. A quadrature gives about 0.06. -/
theorem leaf_variation_middle_integral {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if ¬(1 ≤ a+3*b) ∧ (99/100:ℝ) ≤ a+3*b then
        (if lowerTwoDiscarded ε a b then (107/200)/(a*b^3) else 0) else 0)) ≤ 1/10 := by
  sorry

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

private theorem low_region {ε a b : ℝ} (hε8 : ε ≤ 1/10^8) (hbr : a + 3*b < 99/100)
    (hD : lowerTwoDiscarded ε a b) :
    (12499/100000:ℝ) ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ a + 2*b ≤ 1 ∧
      (56249/100000:ℝ) ≤ a + 2*b ∧ b < 1/4 := by
  obtain ⟨hb, hba, ha, hs, hne⟩ := hD
  have he1 : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε) :=
    fun h => hne (Or.inl h)
  refine ⟨by linarith, hba, ha, hs, by linarith, by linarith⟩

private theorem inv_le_secant {m U a : ℝ} (hm : 0 < m) (hU : 0 < U) (ha1 : m ≤ a) (ha2 : a ≤ U) :
    1/a ≤ 1/m - (a-m)/(m*U) := by
  have ha : 0 < a := by linarith
  have hkey : (0:ℝ) ≤ (a-m)*(U-a) := mul_nonneg (by linarith) (by linarith)
  rw [div_le_iff₀ ha]
  field_simp
  nlinarith [hkey]

private theorem secant_nonneg {m U a : ℝ} (hm : 0 < m) (hU : 0 < U) (ha1 : m ≤ a) (ha2 : a ≤ U + m) :
    (0:ℝ) ≤ 1/m - (a-m)/(m*U) := by
  have h3 : (a-m)/(m*U) ≤ 1/m := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < m*U)]
    have h4 : (m*U)*(1/m) = U := by field_simp
    nlinarith
  linarith

private theorem secant_integral {m U : ℝ} (hm : 0 < m) (hU : 0 < U) :
    (∫ a in m..U, (1/m - (a-m)/(m*U))) = (U-m)/m - (U-m)^2/(2*m*U) := by
  have hc1 : IntervalIntegrable (fun a : ℝ => (1/m:ℝ)) volume m U :=
    continuous_const.intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun a : ℝ => (a-m)/(m*U)) volume m U :=
    (by fun_prop : Continuous fun a : ℝ => (a-m)/(m*U)).intervalIntegrable _ _
  have hc3 : IntervalIntegrable (fun a : ℝ => a) volume m U :=
    continuous_id.intervalIntegrable _ _
  have hc4 : IntervalIntegrable (fun _ : ℝ => m) volume m U :=
    continuous_const.intervalIntegrable _ _
  have hstep : (∫ a in m..U, ((a-m)/(m*U))) = (m*U)⁻¹ * ∫ a in m..U, (a - m) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun a _ => by rw [div_eq_inv_mul])
  have hsub : (∫ a in m..U, (a - m)) = (∫ a in m..U, a) - ∫ _ in m..U, m :=
    intervalIntegral.integral_sub hc3 hc4
  have hid : (∫ a in m..U, a) = (U^2 - m^2)/2 := by
    simpa using integral_pow (a := m) (b := U) 1
  rw [intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const, hstep, hsub, hid,
    intervalIntegral.integral_const]
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hU0 : U ≠ 0 := ne_of_gt hU
  simp only [smul_eq_mul]
  field_simp
  ring

private theorem step_measurable (P : ℝ → Prop) (hP : MeasurableSet P) :
    Measurable (fun a : ℝ => if P a then 1/a else 0) :=
  Measurable.ite hP (by fun_prop) measurable_const

private theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} {lo hi M : ℝ}
    (hm : Measurable f) (h1 : ∀ x ∈ Set.Ioc lo hi, ‖f x‖ ≤ M)
    (h2 : ∀ x ∈ Set.Ioc hi lo, ‖f x‖ ≤ M) :
    IntervalIntegrable f volume lo hi := by
  refine ⟨Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_,
    Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      hm.aestronglyMeasurable ?_⟩
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact h1 x hx
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact h2 x hx

private theorem intervalIntegrable_of_bounded_Icc {f : ℝ → ℝ} {M : ℝ}
    (hm : Measurable f) (hM : ∀ x, ‖f x‖ ≤ M) (lo hi : ℝ) :
    IntervalIntegrable f volume lo hi :=
  intervalIntegrable_of_bounded hm (fun x _ => hM x) (fun x _ => hM x)

private theorem sliceintegrable {m U : ℝ} (hm : 0 < m) (lo hi : ℝ) :
    IntervalIntegrable (fun a : ℝ => if m ≤ a ∧ a ≤ U then 1/a else 0) volume lo hi := by
  refine intervalIntegrable_of_bounded_Icc (M := 1/m) ?_ (fun x => ?_) lo hi
  · exact Measurable.ite (measurableSet_le measurable_const measurable_id |>.inter
      (measurableSet_le measurable_id measurable_const)) (by fun_prop) measurable_const
  · rw [Real.norm_eq_abs]
    by_cases h : m ≤ x ∧ x ≤ U
    · rw [ite_eq_left h, abs_of_pos (div_pos one_pos (by linarith [h.1]))]
      exact one_div_le_one_div_of_le hm h.1
    · rw [ite_eq_right h, abs_zero]; positivity

private theorem step_intervalIntegrable (P : ℝ → Prop) (hP : MeasurableSet P) {m : ℝ}
    (hm : 0 < m) (hle : ∀ a, P a → m ≤ a) (lo hi : ℝ) :
    IntervalIntegrable (fun a : ℝ => if P a then 1/a else 0) volume lo hi := by
  refine intervalIntegrable_of_bounded_Icc (step_measurable P hP) (M := 1/m) (fun x => ?_) lo hi
  rw [Real.norm_eq_abs]
  by_cases hx : P x
  · rw [ite_eq_left hx, abs_of_pos (div_pos one_pos (by linarith [hle x hx]))]
    exact one_div_le_one_div_of_le hm (hle x hx)
  · rw [ite_eq_right hx, abs_zero]
    positivity

private theorem slice_vanishes_left {m U : ℝ} {lo : ℝ} (hlo : lo ≤ m) :
    (∫ a in lo..m, (if m ≤ a ∧ a ≤ U then 1/a else 0)) = 0 := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ m := by
    have h : ({m} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := by
      rw [MeasureTheory.compl_mem_ae_iff]
      exact MeasureTheory.measure_singleton m
    exact h
  rw [show (∫ a in lo..m, (if m ≤ a ∧ a ≤ U then 1/a else 0))
      = ∫ a in lo..m, ((0:ℝ)) from
    intervalIntegral.integral_congr_ae (by
      filter_upwards [hne] with x hx hmem
      rw [ite_eq_right]
      intro h
      have h1 : x ≤ m := by
        have h2 : x ∈ Set.uIoc lo m := hmem
        rw [Set.uIoc_of_le hlo] at h2
        exact h2.2
      exact hx (le_antisymm h1 h.1))]
  exact intervalIntegral.integral_zero

private theorem empty_slice_integrable {c d : ℝ} (hd : d ≤ 0) :
    IntervalIntegrable (fun a : ℝ => if c ≤ a ∧ a ≤ d then 1/a else 0) volume (1/10) (1/2) := by
  refine intervalIntegrable_of_bounded (M := 10) ?_ (fun x hx => ?_) (fun x hx => ?_)
  · exact Measurable.ite (measurableSet_le measurable_const measurable_id |>.inter
      (measurableSet_le measurable_id measurable_const)) (by fun_prop) measurable_const
  · rw [show (if c ≤ x ∧ x ≤ d then 1/x else 0) = 0 from by
      rw [ite_eq_right]
      intro h
      linarith [h.2, hd, hx.1]]
    simp
  · exfalso; linarith [hx.1, hx.2]

private theorem slice_trapezoid {m U : ℝ} (hm : 0 < m) (hmU : m < U)
    (hm1 : (1/10:ℝ) ≤ m) (hU2 : U ≤ 1/2) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), (if m ≤ a ∧ a ≤ U then 1/a else 0))
      ≤ (U-m)/m - (U-m)^2/(2*m*U) := by
  have hU : 0 < U := by linarith
  have key : ∀ (x y : ℝ), IntervalIntegrable (fun a : ℝ => if m ≤ a ∧ a ≤ U then 1/a else 0)
      volume x y :=
    fun x y => sliceintegrable hm x y
  have hL : (∫ a in (1/10:ℝ)..m, (if m ≤ a ∧ a ≤ U then 1/a else 0)) = 0 :=
    slice_vanishes_left (U := U) (by linarith)
  have hR : (∫ a in U..(1/2:ℝ), (if m ≤ a ∧ a ≤ U then 1/a else 0)) = 0 := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ U := by
      have h : ({U} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := by
        rw [MeasureTheory.compl_mem_ae_iff]
        exact MeasureTheory.measure_singleton U
      exact h
    rw [show (∫ a in U..(1/2:ℝ), (if m ≤ a ∧ a ≤ U then 1/a else 0))
        = ∫ a in U..(1/2:ℝ), ((0:ℝ)) from
      intervalIntegral.integral_congr_ae (by
        filter_upwards [hne] with x hx hmem
        rw [ite_eq_right]
        intro h
        have h1 : U ≤ x := by
          have h2 : x ∈ Set.uIoc U (1/2) := hmem
          rw [Set.uIoc_of_le (by linarith)] at h2
          exact le_of_lt h2.1
        exact hx (le_antisymm h.2 h1))]
    exact intervalIntegral.integral_zero
  have hmid : (∫ a in m..U, (if m ≤ a ∧ a ≤ U then 1/a else 0))
      ≤ ∫ a in m..U, (1/m - (a-m)/(m*U)) := by
    apply intervalIntegral.integral_mono_on (by linarith) (key m U)
    · exact (by fun_prop : Continuous fun a : ℝ => 1/m - (a-m)/(m*U)).intervalIntegrable _ _
    · intro a ha
      by_cases h : m ≤ a ∧ a ≤ U
      · rw [ite_eq_left h]
        exact inv_le_secant hm hU h.1 h.2
      · rw [ite_eq_right h]
        exact secant_nonneg hm hU ha.1 (by linarith [ha.2])
  have hA := intervalIntegral.integral_add_adjacent_intervals (key (1/10) m) (key m U)
  have hB := intervalIntegral.integral_add_adjacent_intervals (key (1/10) U) (key U (1/2))
  rw [hL] at hA
  rw [hR] at hB
  have htot : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if m ≤ a ∧ a ≤ U then 1/a else 0))
      = ∫ a in m..U, (if m ≤ a ∧ a ≤ U then 1/a else 0) := by linarith
  rw [htot]
  exact hmid.trans (le_of_eq (secant_integral hm hU))

private theorem inv_cube_integrable {B0 B1 : ℝ} (hB0 : 0 < B0) (hB1 : B0 ≤ B1) :
    IntervalIntegrable (fun b : ℝ => (b^3)⁻¹) volume B0 B1 := by
  refine intervalIntegrable_of_bounded (M := (B0^3)⁻¹) (by fun_prop) (fun x hx => ?_)
    (fun x hx => ?_)
  · have hx0 : (0:ℝ) < x := lt_of_lt_of_le hB0 (le_of_lt hx.1)
    have hx1 : B0^3 ≤ x^3 := pow_le_pow_left₀ (le_of_lt hB0) (le_of_lt hx.1) 3
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (x^3)⁻¹)]
    exact inv_anti₀ (by positivity : (0:ℝ) < B0^3) hx1
  · exfalso; linarith [hx.1, hx.2]

private theorem integral_inv_cube {B0 B1 : ℝ} (hB0 : 0 < B0) (hB1 : B0 ≤ B1) :
    (∫ b in B0..B1, (b^3)⁻¹) = 1/(2*B0^2) - 1/(2*B1^2) := by
  have h0 : (0:ℝ) ∉ Set.uIcc B0 B1 := by
    rw [Set.mem_uIcc]; rintro (h | h) <;> linarith
  have h := integral_zpow (a := B0) (b := B1) (n := -3) (Or.inr ⟨by norm_num, h0⟩)
  have hcongr : (∫ b in B0..B1, (b^3)⁻¹) = ∫ b in B0..B1, (b:ℝ)^(-3:ℤ) := by
    apply intervalIntegral.integral_congr
    intro b _; simp
  rw [hcongr, h]
  rw [show ((-3:ℤ) + 1) = (-2:ℤ) from by norm_num]
  simp only [zpow_neg, zpow_ofNat]
  have hB00 : B0 ≠ 0 := ne_of_gt hB0
  have hB10 : B1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

private theorem low_measurable (ε : ℝ) :
    Measurable (fun p : ℝ × ℝ => if p.1 + 3*p.2 < 99/100 then
      (if lowerTwoDiscarded ε p.1 p.2 then (7/200)/(p.1*p.2^3) else 0) else 0) :=
  Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    (Measurable.ite (two_density_region_measurable ε) (by fun_prop) measurable_const)
    measurable_const

private theorem low_measurable_b (ε a : ℝ) :
    Measurable (fun b : ℝ => if a + 3*b < 99/100 then
      (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0) :=
  Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    (Measurable.ite ((two_density_region_measurable ε).preimage
      (measurable_const.prodMk measurable_id)) (by fun_prop) measurable_const) measurable_const

private theorem low_abs_bound {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a b : ℝ) :
    |(if a + 3*b < 99/100 then
      (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)| ≤ 350 := by
  by_cases h1 : a + 3*b < 99/100
  · by_cases h2 : lowerTwoDiscarded ε a b
    · rw [ite_eq_left h1, ite_eq_left h2]
      obtain ⟨hb, hba, ha, hs, hal, hbq⟩ := low_region hε8 h1 h2
      have ha1 : (1/10:ℝ) ≤ a := by linarith
      have hb1 : (1/10:ℝ) ≤ b := by linarith
      have hb3 : (1/10:ℝ)^3 ≤ b^3 := pow_le_pow_left₀ (by norm_num) hb1 3
      have hprod : (1/10000:ℝ) ≤ a*b^3 := by
        have h2' : (1/10:ℝ)*(1/10:ℝ)^3 ≤ a*b^3 :=
          mul_le_mul ha1 hb3 (by positivity) (by linarith)
        linarith
      have hpos : (0:ℝ) < a*b^3 := by linarith
      rw [abs_of_pos (div_pos (by norm_num : (0:ℝ) < 7/200) hpos)]
      rw [div_le_iff₀ hpos]
      nlinarith
    · rw [ite_eq_left h1, ite_eq_right h2]; norm_num
  · rw [ite_eq_right h1]; norm_num

private theorem low_left_zero {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a c : ℝ)
    (hc : (1/10:ℝ) ≤ c) (hc2 : c ≤ 12499/100000) :
    (∫ b in (1/10:ℝ)..c, (if a+3*b < 99/100 then
      (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ 0 := by
  have hint : IntervalIntegrable (fun b : ℝ => (if a+3*b < 99/100 then
      (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) volume (1/10) c :=
    intervalIntegrable_of_bounded_Icc (low_measurable_b ε a)
      (fun x => by rw [Real.norm_eq_abs]; exact low_abs_bound hε8 a x) _ _
  have h0 : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume (1/10) c :=
    continuous_const.intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hc hint h0
    (fun b hb => by
      by_cases hbr : a + 3*b < 99/100
      · rw [ite_eq_left hbr, ite_eq_right]
        intro hD
        have hr := low_region hε8 hbr hD
        linarith [hr.1, hb.2]
      · rw [ite_eq_right hbr])
  simpa using h

private theorem low_right_zero {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a c : ℝ)
    (hc : (1/4:ℝ) ≤ c) (hc2 : c ≤ 1/2) :
    (∫ b in c..(1/2:ℝ), (if a+3*b < 99/100 then
      (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ 0 := by
  have hint : IntervalIntegrable (fun b : ℝ => (if a+3*b < 99/100 then
      (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) volume c (1/2) :=
    intervalIntegrable_of_bounded_Icc (low_measurable_b ε a)
      (fun x => by rw [Real.norm_eq_abs]; exact low_abs_bound hε8 a x) _ _
  have h0 : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume c (1/2) :=
    continuous_const.intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hc2 hint h0
    (fun b hb => by
      by_cases hbr : a + 3*b < 99/100
      · rw [ite_eq_left hbr, ite_eq_right]
        intro hD
        obtain ⟨-, -, -, -, -, hbq⟩ := low_region hε8 hbr hD
        linarith [hbq, hb.1]
      · rw [ite_eq_right hbr])
  simpa using h

private theorem low_strip {ε a B0 B1 : ℝ} (hε8 : ε ≤ 1/10^8) (ha : 0 < a)
    {m1 U1 m2 U2 m3 U3 : ℝ} (hB0 : 0 < B0) (hB1 : B0 ≤ B1)
    (hsup : ∀ b, b ∈ Ioo B0 B1 → a + 3*b < 99/100 → lowerTwoDiscarded ε a b →
      (m1 ≤ a ∧ a ≤ U1) ∨ (m2 ≤ a ∧ a ≤ U2) ∨ (m3 ≤ a ∧ a ≤ U3)) :
    (∫ b in B0..B1, (if a+3*b < 99/100 then
        (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ (7/200) * (1/(2*B0^2) - 1/(2*B1^2)) *
        ((if m1 ≤ a ∧ a ≤ U1 then 1/a else 0) + (if m2 ≤ a ∧ a ≤ U2 then 1/a else 0) +
          (if m3 ≤ a ∧ a ≤ U3 then 1/a else 0)) := by
  set S : ℝ := ((if m1 ≤ a ∧ a ≤ U1 then (1:ℝ) else 0) + (if m2 ≤ a ∧ a ≤ U2 then 1 else 0) +
    (if m3 ≤ a ∧ a ≤ U3 then 1 else 0)) with hSdef
  have hInd : ∀ (m U : ℝ), (0:ℝ) ≤ (if m ≤ a ∧ a ≤ U then (1:ℝ) else 0) := by
    intro m U; split <;> norm_num
  have hSnn : (0:ℝ) ≤ S := by
    rw [hSdef]; have e1 := hInd m1 U1; have e2 := hInd m2 U2; have e3 := hInd m3 U3; linarith
  have hca : (0:ℝ) < (7/200)/a := by positivity
  have hpt : ∀ b ∈ Ioo B0 B1, (if a+3*b < 99/100 then
        (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)
      ≤ ((7/200)/a * S) * (b^3)⁻¹ := by
    intro b hb
    have hb0 : (0:ℝ) < b := lt_trans hB0 hb.1
    have hb3 : (0:ℝ) ≤ (b^3)⁻¹ := by positivity
    by_cases h1 : a+3*b < 99/100
    · by_cases h2 : lowerTwoDiscarded ε a b
      · rw [ite_eq_left h1, ite_eq_left h2]
        have hS1 : (1:ℝ) ≤ S := by
          rw [hSdef]
          rcases hsup b hb h1 h2 with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
          · rw [ite_eq_left (show m1 ≤ a ∧ a ≤ U1 from ⟨h, h'⟩)]
            have e2 := hInd m2 U2; have e3 := hInd m3 U3; linarith
          · rw [ite_eq_left (show m2 ≤ a ∧ a ≤ U2 from ⟨h, h'⟩)]
            have e1 := hInd m1 U1; have e3 := hInd m3 U3; linarith
          · rw [ite_eq_left (show m3 ≤ a ∧ a ≤ U3 from ⟨h, h'⟩)]
            have e1 := hInd m1 U1; have e2 := hInd m2 U2; linarith
        have heq : (7/200)/(a*b^3) = ((7/200)/a) * (b^3)⁻¹ := by
          rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
          ring
        rw [heq]
        have hstep : ((7/200)/a) * (b^3)⁻¹ ≤ ((7/200)/a * S) * (b^3)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hb3
          calc ((7/200)/a) = ((7/200)/a) * 1 := by ring
            _ ≤ ((7/200)/a) * S := mul_le_mul_of_nonneg_left hS1 hca.le
        exact hstep
      · rw [ite_eq_left h1, ite_eq_right h2]
        exact mul_nonneg (mul_nonneg hca.le hSnn) hb3
    · rw [ite_eq_right h1]
      exact mul_nonneg (mul_nonneg hca.le hSnn) hb3
  have hint : IntervalIntegrable (fun b : ℝ => ((7/200)/a * S) * (b^3)⁻¹) volume B0 B1 :=
    (inv_cube_integrable hB0 hB1).const_mul ((7/200)/a * S)
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hB1
    (intervalIntegrable_of_bounded_Icc (low_measurable_b ε a)
      (fun x => by rw [Real.norm_eq_abs]; exact low_abs_bound hε8 a x) _ _)
    hint hpt
  have hfac : (∫ b in B0..B1, ((7/200)/a * S) * (b^3)⁻¹)
      = ((7/200)/a * S) * (1/(2*B0^2) - 1/(2*B1^2)) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_cube hB0 hB1]
  rw [hfac] at hmono
  refine hmono.trans (le_of_eq ?_)
  have key : ∀ c d : ℝ, (if c ≤ a ∧ a ≤ d then (1:ℝ) else 0) =
      a * (if c ≤ a ∧ a ≤ d then 1/a else 0) := by
    intro c d
    by_cases h : c ≤ a ∧ a ≤ d
    · rw [ite_eq_left h, ite_eq_left h, mul_one_div_cancel (ne_of_gt ha)]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [hSdef, key m1 U1, key m2 U2, key m3 U3]
  field_simp


private theorem empty_slice_le_zero {c d : ℝ} (hd : d ≤ 0) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), (if c ≤ a ∧ a ≤ d then 1/a else 0)) ≤ 0 := by
  rw [show (∫ a in (1/10:ℝ)..(1/2:ℝ), (if c ≤ a ∧ a ≤ d then 1/a else 0))
      = ∫ a in (1/10:ℝ)..(1/2:ℝ), ((0:ℝ)) from
    intervalIntegral.integral_congr (fun a ha => by
      rw [ite_eq_right]
      intro h
      have h1 : (1/10:ℝ) ≤ a := by
        rw [Set.uIcc_of_le (by norm_num)] at ha
        exact ha.1
      linarith [h.2])]
  exact le_of_eq intervalIntegral.integral_zero

private theorem cover_0 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (12499/100000:ℝ) ≤ b) (hb1 : b ≤ (135211/1000000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ)) ∨
    ((1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ)) ∨
    ((1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_1 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (135211/1000000:ℝ) ≤ b) (hb1 : b ≤ (18179/125000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ)) ∨
    ((844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ)) ∨
    ((989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_2 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (18179/125000:ℝ) ≤ b) (hb1 : b ≤ (155653/1000000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ)) ∨
    ((1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ)) ∨
    ((1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_3 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (155653/1000000:ℝ) ≤ b) (hb1 : b ≤ (82937/500000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ)) ∨
    ((406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ)) ∨
    ((244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_4 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (82937/500000:ℝ) ≤ b) (hb1 : b ≤ (35219/200000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ)) ∨
    ((319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ)) ∨
    ((15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_5 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (35219/200000:ℝ) ≤ b) (hb1 : b ≤ (46579/250000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ)) ∨
    ((783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_6 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (46579/250000:ℝ) ≤ b) (hb1 : b ≤ (196537/1000000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ)) ∨
    ((1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_7 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (196537/1000000:ℝ) ≤ b) (hb1 : b ≤ (103379/500000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ)) ∨
    ((188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_8 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (103379/500000:ℝ) ≤ b) (hb1 : b ≤ (216979/1000000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ)) ∨
    ((1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_9 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (216979/1000000:ℝ) ≤ b) (hb1 : b ≤ (142/625:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) := by
  have hbc : (1 + 7*(2*(1/16 - 1/10^5)))/15 - ε ≤ b := hD.1
  have hne : ¬(a + 2*b ≤ 1/2 + (1 + 22*(2*(1/16 - 1/10^5)))/60 - 2*ε ∨
      4*a + 7*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
        1/2 - (2*(1/16 - 1/10^5) + 3*((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε ∧
        4*a + 5*b ≤ 2 + 2*(1/16 - 1/10^5) - ε ∧
          1/2 - (2*(1/16 - 1/10^5) + ((1 + 7*(2*(1/16 - 1/10^5)))/15 - ε))/4 + ε ≤ a + b ∨
      upperPairRegion ε a b) := hD.2.2.2.2
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  have hbB : b ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε := by linarith
  have hup : ¬ upperPairRegion ε a b := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  unfold upperPairRegion at hup
  have hkey : ¬((2*b - (2*(1/16 - 1/10^5)) + ε ≤ a ∧
        a ≤ (36*(2*(1/16 - 1/10^5)) - 2)/11 - ε) ∨
      |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε ∨ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε) := by
    intro h; exact hup ⟨hba, ha, hbc, hbB, h⟩
  have h3 : 4*a + 3*b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + 3*b := by
    have h1 : ¬ |4*a + 3*b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inl h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + 3*b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + 3*b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  have h4 : 4*a + b < 2 - 2*(1/16 - 1/10^5) + ε ∨ 2 + 2*(1/16 - 1/10^5) - ε < 4*a + b := by
    have h1 : ¬ |4*a + b - 2| ≤ 2*(1/16 - 1/10^5) - ε := fun h => hkey (Or.inr (Or.inr h))
    have h2 : 2*(1/16 - 1/10^5) - ε < |4*a + b - 2| := lt_of_not_ge h1
    rcases lt_trichotomy (4*a + b - 2) 0 with hp | hp | hp
    · rw [abs_of_neg hp] at h2
      left; linarith
    · rw [hp] at h2; simp at h2; linarith
    · rw [abs_of_pos hp] at h2
      right; linarith
  rcases h3 with h3 | h3
  · rcases h4 with h4 | h4
    · left; constructor <;> linarith
    · right; right; constructor <;> linarith
  · rcases h4 with h4 | h4
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

private theorem cover_10 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (142/625:ℝ) ≤ b) (hb1 : b ≤ (1193/5000:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) := by
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  exact Or.inl ⟨by linarith, by linarith⟩

private theorem cover_11 {ε a b : ℝ} (hε8 : ε ≤ 1/10^8)
    (hb0 : (1193/5000:ℝ) ≤ b) (hb1 : b ≤ (1/4:ℝ))
    (hbr : a + 3*b < 99/100) (hD : lowerTwoDiscarded ε a b) :
    ((1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) ∨
    ((0:ℝ) ≤ a ∧ a ≤ (0:ℝ)) := by
  obtain ⟨-, hba, ha, hs, hal, hbq⟩ := low_region hε8 hbr hD
  exact Or.inl ⟨by linarith, by linarith⟩


private theorem strip_0 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (12499/100000:ℝ)..(135211/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (12499/100000:ℝ)) (B1 := (135211/1000000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_0 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_1 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (135211/1000000:ℝ)..(18179/125000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (135211/1000000:ℝ)) (B1 := (18179/125000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_1 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_2 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (18179/125000:ℝ)..(155653/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (18179/125000:ℝ)) (B1 := (155653/1000000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_2 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_3 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (155653/1000000:ℝ)..(82937/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (155653/1000000:ℝ)) (B1 := (82937/500000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_3 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_4 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (82937/500000:ℝ)..(35219/200000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (82937/500000:ℝ)) (B1 := (35219/200000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_4 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_5 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (35219/200000:ℝ)..(46579/250000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (35219/200000:ℝ)) (B1 := (46579/250000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_5 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_6 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (46579/250000:ℝ)..(196537/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (46579/250000:ℝ)) (B1 := (196537/1000000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_6 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_7 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (196537/1000000:ℝ)..(103379/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (196537/1000000:ℝ)) (B1 := (103379/500000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_7 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_8 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (103379/500000:ℝ)..(216979/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (103379/500000:ℝ)) (B1 := (216979/1000000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_8 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_9 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (216979/1000000:ℝ)..(142/625:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (216979/1000000:ℝ)) (B1 := (142/625:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_9 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_10 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (142/625:ℝ)..(1193/5000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (142/625:ℝ)) (B1 := (1193/5000:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_10 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem strip_11 {ε : ℝ} (hε8 : ε ≤ 1/10^8) {a : ℝ} (ha : 0 < a) :
    (∫ b in (1193/5000:ℝ)..(1/4:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := by
  apply low_strip (ε := ε) (a := a) (B0 := (1193/5000:ℝ)) (B1 := (1/4:ℝ)) hε8 ha
    (by norm_num) (by norm_num)
  intro b hb hbr hD
  exact cover_11 hε8 (le_of_lt hb.1) (le_of_lt hb.2) hbr hD

private theorem phibound_0 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((((75003/200000:ℝ) - (73017/250000:ℝ))/(73017/250000:ℝ) - ((75003/200000:ℝ) - (73017/250000:ℝ))^2/(2*(73017/250000:ℝ)*(75003/200000:ℝ))) + (((43751/100000:ℝ) - (1719337/4000000:ℝ))/(1719337/4000000:ℝ) - ((43751/100000:ℝ) - (1719337/4000000:ℝ))^2/(2*(1719337/4000000:ℝ)*(43751/100000:ℝ))) + (((1/2:ℝ) - (1989759/4000000:ℝ))/(1989759/4000000:ℝ) - ((1/2:ℝ) - (1989759/4000000:ℝ))^2/(2*(1989759/4000000:ℝ)*(1/2:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) +
        (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (73017/250000:ℝ)) (U := (75003/200000:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (1719337/4000000:ℝ)) (U := (43751/100000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) +
          (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (73017/250000:ℝ)) (U := (75003/200000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (1719337/4000000:ℝ)) (U := (43751/100000:ℝ)) (by norm_num) (1/10) (1/2))) (sliceintegrable (m := (1989759/4000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (1/10) (1/2))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (73017/250000:ℝ)) (U := (75003/200000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (1719337/4000000:ℝ)) (U := (43751/100000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := slice_trapezoid (m := (1989759/4000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_1 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((((1469397/4000000:ℝ) - (135813/500000:ℝ))/(135813/500000:ℝ) - ((1469397/4000000:ℝ) - (135813/500000:ℝ))^2/(2*(135813/500000:ℝ)*(1469397/4000000:ℝ))) + (((1739819/4000000:ℝ) - (844337/2000000:ℝ))/(844337/2000000:ℝ) - ((1739819/4000000:ℝ) - (844337/2000000:ℝ))^2/(2*(844337/2000000:ℝ)*(1739819/4000000:ℝ))) + (((1/2:ℝ) - (989769/2000000:ℝ))/(989769/2000000:ℝ) - ((1/2:ℝ) - (989769/2000000:ℝ))^2/(2*(989769/2000000:ℝ)*(1/2:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) +
        (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (135813/500000:ℝ)) (U := (1469397/4000000:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (844337/2000000:ℝ)) (U := (1739819/4000000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) +
          (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (135813/500000:ℝ)) (U := (1469397/4000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (844337/2000000:ℝ)) (U := (1739819/4000000:ℝ)) (by norm_num) (1/10) (1/2))) (sliceintegrable (m := (989769/2000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (1/10) (1/2))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (135813/500000:ℝ)) (U := (1469397/4000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (844337/2000000:ℝ)) (U := (1739819/4000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := slice_trapezoid (m := (989769/2000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_2 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((((719367/2000000:ℝ) - (15699/62500:ℝ))/(15699/62500:ℝ) - ((719367/2000000:ℝ) - (15699/62500:ℝ))^2/(2*(15699/62500:ℝ)*(719367/2000000:ℝ))) + (((864799/2000000:ℝ) - (1658011/4000000:ℝ))/(1658011/4000000:ℝ) - ((864799/2000000:ℝ) - (1658011/4000000:ℝ))^2/(2*(1658011/4000000:ℝ)*(864799/2000000:ℝ))) + (((1/2:ℝ) - (1969317/4000000:ℝ))/(1969317/4000000:ℝ) - ((1/2:ℝ) - (1969317/4000000:ℝ))^2/(2*(1969317/4000000:ℝ)*(1/2:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) +
        (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (15699/62500:ℝ)) (U := (719367/2000000:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (1658011/4000000:ℝ)) (U := (864799/2000000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) +
          (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (15699/62500:ℝ)) (U := (719367/2000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (1658011/4000000:ℝ)) (U := (864799/2000000:ℝ)) (by norm_num) (1/10) (1/2))) (sliceintegrable (m := (1969317/4000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (1/10) (1/2))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (15699/62500:ℝ)) (U := (719367/2000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (1658011/4000000:ℝ)) (U := (864799/2000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := slice_trapezoid (m := (1969317/4000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_3 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((((1408071/4000000:ℝ) - (115371/500000:ℝ))/(115371/500000:ℝ) - ((1408071/4000000:ℝ) - (115371/500000:ℝ))^2/(2*(115371/500000:ℝ)*(1408071/4000000:ℝ))) + (((1719377/4000000:ℝ) - (406837/1000000:ℝ))/(406837/1000000:ℝ) - ((1719377/4000000:ℝ) - (406837/1000000:ℝ))^2/(2*(406837/1000000:ℝ)*(1719377/4000000:ℝ))) + (((1/2:ℝ) - (244887/500000:ℝ))/(244887/500000:ℝ) - ((1/2:ℝ) - (244887/500000:ℝ))^2/(2*(244887/500000:ℝ)*(1/2:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) +
        (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (115371/500000:ℝ)) (U := (1408071/4000000:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (406837/1000000:ℝ)) (U := (1719377/4000000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) +
          (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (115371/500000:ℝ)) (U := (1408071/4000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (406837/1000000:ℝ)) (U := (1719377/4000000:ℝ)) (by norm_num) (1/10) (1/2))) (sliceintegrable (m := (244887/500000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (1/10) (1/2))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (115371/500000:ℝ)) (U := (1408071/4000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (406837/1000000:ℝ)) (U := (1719377/4000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := slice_trapezoid (m := (244887/500000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_4 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((((10761/31250:ℝ) - (2103/10000:ℝ))/(2103/10000:ℝ) - ((10761/31250:ℝ) - (2103/10000:ℝ))^2/(2*(2103/10000:ℝ)*(10761/31250:ℝ))) + (((427289/1000000:ℝ) - (319337/800000:ℝ))/(319337/800000:ℝ) - ((427289/1000000:ℝ) - (319337/800000:ℝ))^2/(2*(319337/800000:ℝ)*(427289/1000000:ℝ))) + (((246189/500000:ℝ) - (15591/32000:ℝ))/(15591/32000:ℝ) - ((246189/500000:ℝ) - (15591/32000:ℝ))^2/(2*(15591/32000:ℝ)*(246189/500000:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) +
        (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (2103/10000:ℝ)) (U := (10761/31250:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (319337/800000:ℝ)) (U := (427289/1000000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) +
          (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (2103/10000:ℝ)) (U := (10761/31250:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (319337/800000:ℝ)) (U := (427289/1000000:ℝ)) (by norm_num) (1/10) (1/2))) (sliceintegrable (m := (15591/32000:ℝ)) (U := (246189/500000:ℝ)) (by norm_num) (1/10) (1/2))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (2103/10000:ℝ)) (U := (10761/31250:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (319337/800000:ℝ)) (U := (427289/1000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := slice_trapezoid (m := (15591/32000:ℝ)) (U := (246189/500000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_5 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((((269349/800000:ℝ) - (94929/500000:ℝ))/(94929/500000:ℝ) - ((269349/800000:ℝ) - (94929/500000:ℝ))^2/(2*(94929/500000:ℝ)*(269349/800000:ℝ))) + (((339787/800000:ℝ) - (783011/2000000:ℝ))/(783011/2000000:ℝ) - ((339787/800000:ℝ) - (783011/2000000:ℝ))^2/(2*(783011/2000000:ℝ)*(339787/800000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) +
        (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (94929/500000:ℝ)) (U := (269349/800000:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (783011/2000000:ℝ)) (U := (339787/800000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) +
          (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (94929/500000:ℝ)) (U := (269349/800000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (783011/2000000:ℝ)) (U := (339787/800000:ℝ)) (by norm_num) (1/10) (1/2))) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (94929/500000:ℝ)) (U := (269349/800000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (783011/2000000:ℝ)) (U := (339787/800000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_6 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((((658041/2000000:ℝ) - (46579/250000:ℝ))/(46579/250000:ℝ) - ((658041/2000000:ℝ) - (46579/250000:ℝ))^2/(2*(46579/250000:ℝ)*(658041/2000000:ℝ))) + (((844357/2000000:ℝ) - (1535359/4000000:ℝ))/(1535359/4000000:ℝ) - ((844357/2000000:ℝ) - (1535359/4000000:ℝ))^2/(2*(1535359/4000000:ℝ)*(844357/2000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) +
        (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (46579/250000:ℝ)) (U := (658041/2000000:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (1535359/4000000:ℝ)) (U := (844357/2000000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) +
          (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (46579/250000:ℝ)) (U := (658041/2000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (1535359/4000000:ℝ)) (U := (844357/2000000:ℝ)) (by norm_num) (1/10) (1/2))) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (46579/250000:ℝ)) (U := (658041/2000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (1535359/4000000:ℝ)) (U := (844357/2000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_7 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((((1285419/4000000:ℝ) - (196537/1000000:ℝ))/(196537/1000000:ℝ) - ((1285419/4000000:ℝ) - (196537/1000000:ℝ))^2/(2*(196537/1000000:ℝ)*(1285419/4000000:ℝ))) + (((400389/1000000:ℝ) - (188087/500000:ℝ))/(188087/500000:ℝ) - ((400389/1000000:ℝ) - (188087/500000:ℝ))^2/(2*(188087/500000:ℝ)*(400389/1000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) +
        (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (196537/1000000:ℝ)) (U := (1285419/4000000:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (188087/500000:ℝ)) (U := (400389/1000000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) +
          (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (196537/1000000:ℝ)) (U := (1285419/4000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (188087/500000:ℝ)) (U := (400389/1000000:ℝ)) (by norm_num) (1/10) (1/2))) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (196537/1000000:ℝ)) (U := (1285419/4000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (188087/500000:ℝ)) (U := (400389/1000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_8 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((((313689/1000000:ℝ) - (103379/500000:ℝ))/(103379/500000:ℝ) - ((313689/1000000:ℝ) - (103379/500000:ℝ))^2/(2*(103379/500000:ℝ)*(313689/1000000:ℝ))) + (((184863/500000:ℝ) - (1474033/4000000:ℝ))/(1474033/4000000:ℝ) - ((184863/500000:ℝ) - (1474033/4000000:ℝ))^2/(2*(1474033/4000000:ℝ)*(184863/500000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) +
        (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (103379/500000:ℝ)) (U := (313689/1000000:ℝ)) (by norm_num) (1/10) (1/2)) (sliceintegrable (m := (1474033/4000000:ℝ)) (U := (184863/500000:ℝ)) (by norm_num) (1/10) (1/2))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) +
          (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (103379/500000:ℝ)) (U := (313689/1000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (1474033/4000000:ℝ)) (U := (184863/500000:ℝ)) (by norm_num) (1/10) (1/2))) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (103379/500000:ℝ)) (U := (313689/1000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := slice_trapezoid (m := (1474033/4000000:ℝ)) (U := (184863/500000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_9 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((((1224093/4000000:ℝ) - (216979/1000000:ℝ))/(216979/1000000:ℝ) - ((1224093/4000000:ℝ) - (216979/1000000:ℝ))^2/(2*(216979/1000000:ℝ)*(1224093/4000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) +
        (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (216979/1000000:ℝ)) (U := (1224093/4000000:ℝ)) (by norm_num) (1/10) (1/2)) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) +
          (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (216979/1000000:ℝ)) (U := (1224093/4000000:ℝ)) (by norm_num) (1/10) (1/2)).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (216979/1000000:ℝ)) (U := (1224093/4000000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have t2 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_10 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((((771/2500:ℝ) - (142/625:ℝ))/(142/625:ℝ) - ((771/2500:ℝ) - (142/625:ℝ))^2/(2*(142/625:ℝ)*(771/2500:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) +
        (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (142/625:ℝ)) (U := (771/2500:ℝ)) (by norm_num) (1/10) (1/2)) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) +
          (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (142/625:ℝ)) (U := (771/2500:ℝ)) (by norm_num) (1/10) (1/2)).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (142/625:ℝ)) (U := (771/2500:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have t2 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phibound_11 {ε : ℝ} :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) ≤ ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((((1371/5000:ℝ) - (1193/5000:ℝ))/(1193/5000:ℝ) - ((1371/5000:ℝ) - (1193/5000:ℝ))^2/(2*(1193/5000:ℝ)*(1371/5000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) := by
  have A : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_const_mul _ _
  rw [A]
  have B1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) +
        (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add (sliceintegrable (m := (1193/5000:ℝ)) (U := (1371/5000:ℝ)) (by norm_num) (1/10) (1/2)) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  have B2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) +
          (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) :=
    intervalIntegral.integral_add ((sliceintegrable (m := (1193/5000:ℝ)) (U := (1371/5000:ℝ)) (by norm_num) (1/10) (1/2)).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))) (empty_slice_integrable (c := 0) (d := 0) (by norm_num))
  rw [B2, B1]
  have t0 := slice_trapezoid (m := (1193/5000:ℝ)) (U := (1371/5000:ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t1 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have t2 := empty_slice_le_zero (c := 0) (d := 0) (by norm_num)
  have hK : (0:ℝ) ≤ (7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2)) := by norm_num
  have h0 := mul_le_mul_of_nonneg_left t0 hK
  have h1 := mul_le_mul_of_nonneg_left t1 hK
  have h2 := mul_le_mul_of_nonneg_left t2 hK
  linarith [h0, h1, h2]

private theorem phiint_0 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (73017/250000:ℝ)) (U := (75003/200000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (1719337/4000000:ℝ)) (U := (43751/100000:ℝ)) (by norm_num) (1/10) (1/2))).add (sliceintegrable (m := (1989759/4000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (1/10) (1/2))).const_mul ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2)))

private theorem phiint_1 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (135813/500000:ℝ)) (U := (1469397/4000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (844337/2000000:ℝ)) (U := (1739819/4000000:ℝ)) (by norm_num) (1/10) (1/2))).add (sliceintegrable (m := (989769/2000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (1/10) (1/2))).const_mul ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2)))

private theorem phiint_2 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (15699/62500:ℝ)) (U := (719367/2000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (1658011/4000000:ℝ)) (U := (864799/2000000:ℝ)) (by norm_num) (1/10) (1/2))).add (sliceintegrable (m := (1969317/4000000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (1/10) (1/2))).const_mul ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2)))

private theorem phiint_3 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (115371/500000:ℝ)) (U := (1408071/4000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (406837/1000000:ℝ)) (U := (1719377/4000000:ℝ)) (by norm_num) (1/10) (1/2))).add (sliceintegrable (m := (244887/500000:ℝ)) (U := (1/2:ℝ)) (by norm_num) (1/10) (1/2))).const_mul ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2)))

private theorem phiint_4 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (2103/10000:ℝ)) (U := (10761/31250:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (319337/800000:ℝ)) (U := (427289/1000000:ℝ)) (by norm_num) (1/10) (1/2))).add (sliceintegrable (m := (15591/32000:ℝ)) (U := (246189/500000:ℝ)) (by norm_num) (1/10) (1/2))).const_mul ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2)))

private theorem phiint_5 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (94929/500000:ℝ)) (U := (269349/800000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (783011/2000000:ℝ)) (U := (339787/800000:ℝ)) (by norm_num) (1/10) (1/2))).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).const_mul ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2)))

private theorem phiint_6 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (46579/250000:ℝ)) (U := (658041/2000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (1535359/4000000:ℝ)) (U := (844357/2000000:ℝ)) (by norm_num) (1/10) (1/2))).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).const_mul ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2)))

private theorem phiint_7 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (196537/1000000:ℝ)) (U := (1285419/4000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (188087/500000:ℝ)) (U := (400389/1000000:ℝ)) (by norm_num) (1/10) (1/2))).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).const_mul ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2)))

private theorem phiint_8 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (103379/500000:ℝ)) (U := (313689/1000000:ℝ)) (by norm_num) (1/10) (1/2)).add (sliceintegrable (m := (1474033/4000000:ℝ)) (U := (184863/500000:ℝ)) (by norm_num) (1/10) (1/2))).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).const_mul ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2)))

private theorem phiint_9 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (216979/1000000:ℝ)) (U := (1224093/4000000:ℝ)) (by norm_num) (1/10) (1/2)).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).const_mul ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2)))

private theorem phiint_10 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (142/625:ℝ)) (U := (771/2500:ℝ)) (by norm_num) (1/10) (1/2)).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).const_mul ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2)))

private theorem phiint_11 {ε : ℝ} :
    IntervalIntegrable (fun a : ℝ => ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) volume (1/10) (1/2) :=
  (((sliceintegrable (m := (1193/5000:ℝ)) (U := (1371/5000:ℝ)) (by norm_num) (1/10) (1/2)).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).add (empty_slice_integrable (c := 0) (d := 0) (by norm_num))).const_mul ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2)))



/-- LEAF: the branch of the majorant taken when `a + 3 b < 99/100`, integrated over the box,
is at most `2/5`. A quadrature gives about 0.14. -/
theorem leaf_variation_low_integral {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if a+3*b < (99/100:ℝ) then
        (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ 2/5 := by

  have hint_b : ∀ a (x y : ℝ), IntervalIntegrable (fun b : ℝ => (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) volume x y := by
    intro a x y
    exact intervalIntegrable_of_bounded_Icc (low_measurable_b ε a)
      (fun x => by rw [Real.norm_eq_abs]; exact low_abs_bound hε8 a x) x y
  have hchain : ∀ a : ℝ, (∫ b in (1/10:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = ((((((((((((((∫ b in (1/10:ℝ)..(12499/100000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (12499/100000:ℝ)..(135211/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (135211/1000000:ℝ)..(18179/125000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (18179/125000:ℝ)..(155653/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (155653/1000000:ℝ)..(82937/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (82937/500000:ℝ)..(35219/200000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (35219/200000:ℝ)..(46579/250000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (46579/250000:ℝ)..(196537/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (196537/1000000:ℝ)..(103379/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (103379/500000:ℝ)..(216979/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (216979/1000000:ℝ)..(142/625:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (142/625:ℝ)..(1193/5000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (1193/5000:ℝ)..(1/4:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) + (∫ b in (1/4:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))) := by
    intro a
    rw [show (∫ b in (1/10:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(1/4:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (1/4:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(1/4:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(1193/5000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (1193/5000:ℝ)..(1/4:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(1193/5000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(142/625:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (142/625:ℝ)..(1193/5000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(142/625:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(216979/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (216979/1000000:ℝ)..(142/625:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(216979/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(103379/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (103379/500000:ℝ)..(216979/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(103379/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(196537/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (196537/1000000:ℝ)..(103379/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(196537/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(46579/250000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (46579/250000:ℝ)..(196537/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(46579/250000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(35219/200000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (35219/200000:ℝ)..(46579/250000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(35219/200000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(82937/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (82937/500000:ℝ)..(35219/200000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(82937/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(155653/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (155653/1000000:ℝ)..(82937/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(155653/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(18179/125000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (18179/125000:ℝ)..(155653/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(18179/125000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(135211/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (135211/1000000:ℝ)..(18179/125000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
    rw [show (∫ b in (1/10:ℝ)..(135211/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) = (∫ b in (1/10:ℝ)..(12499/100000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) + (∫ b in (12499/100000:ℝ)..(135211/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) from
      (intervalIntegral.integral_add_adjacent_intervals (hint_b a _ _) (hint_b a _ _)).symm]
  have hstep : ∀ a ∈ Set.Ioo (1/10:ℝ) (1/2:ℝ),
      (∫ b in (1/10:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ (((((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) := by
    intro a ha
    rw [hchain a]
    have z0 : (∫ b in (1/10:ℝ)..(12499/100000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ 0 := low_left_zero hε8 a (12499/100000:ℝ) (by norm_num) (by norm_num)
    have zL : (∫ b in (1/4:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ 0 := low_right_zero hε8 a (1/4) (by norm_num) (by norm_num)
    have ha0 : (0:ℝ) < a := by linarith [ha.1]
    have r0 : (∫ b in (12499/100000:ℝ)..(135211/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) := strip_0 hε8 ha0
    have r1 : (∫ b in (135211/1000000:ℝ)..(18179/125000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) := strip_1 hε8 ha0
    have r2 : (∫ b in (18179/125000:ℝ)..(155653/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) := strip_2 hε8 ha0
    have r3 : (∫ b in (155653/1000000:ℝ)..(82937/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) := strip_3 hε8 ha0
    have r4 : (∫ b in (82937/500000:ℝ)..(35219/200000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) := strip_4 hε8 ha0
    have r5 : (∫ b in (35219/200000:ℝ)..(46579/250000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := strip_5 hε8 ha0
    have r6 : (∫ b in (46579/250000:ℝ)..(196537/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := strip_6 hε8 ha0
    have r7 : (∫ b in (196537/1000000:ℝ)..(103379/500000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := strip_7 hε8 ha0
    have r8 : (∫ b in (103379/500000:ℝ)..(216979/1000000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := strip_8 hε8 ha0
    have r9 : (∫ b in (216979/1000000:ℝ)..(142/625:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := strip_9 hε8 ha0
    have r10 : (∫ b in (142/625:ℝ)..(1193/5000:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := strip_10 hε8 ha0
    have r11 : (∫ b in (1193/5000:ℝ)..(1/4:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) := strip_11 hε8 ha0
    linarith [z0, zL, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11]
  have h4F := four_density_level (fun (x : ℝ) (y : ℝ) => (if x+3*y < 99/100 then
      (if lowerTwoDiscarded ε x y then (7/200)/(x*y^3) else 0) else 0)) (low_measurable ε)
    (fun x y => low_abs_bound hε8 x y) (1/10) (1/2)
  have hIntF : IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) volume (1/10) (1/2) := by
    refine intervalIntegrable_of_bounded_Icc h4F.1 (M := 140) (fun a => ?_) _ _
    have hh := h4F.2 a
    have h2 : (350:ℝ) * |(1/2:ℝ) - 1/10| = 140 := by norm_num
    have h3 := abs_nonneg (∫ b in (1/10:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
    rw [Real.norm_eq_abs]
    linarith
  have hT0 := phiint_0 (ε := ε)
  have hT1 : IntervalIntegrable (fun a : ℝ => (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT0.add (phiint_1 (ε := ε))
  have hT2 : IntervalIntegrable (fun a : ℝ => ((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT1.add (phiint_2 (ε := ε))
  have hT3 : IntervalIntegrable (fun a : ℝ => (((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT2.add (phiint_3 (ε := ε))
  have hT4 : IntervalIntegrable (fun a : ℝ => ((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT3.add (phiint_4 (ε := ε))
  have hT5 : IntervalIntegrable (fun a : ℝ => (((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT4.add (phiint_5 (ε := ε))
  have hT6 : IntervalIntegrable (fun a : ℝ => ((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT5.add (phiint_6 (ε := ε))
  have hT7 : IntervalIntegrable (fun a : ℝ => (((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT6.add (phiint_7 (ε := ε))
  have hT8 : IntervalIntegrable (fun a : ℝ => ((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT7.add (phiint_8 (ε := ε))
  have hT9 : IntervalIntegrable (fun a : ℝ => (((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT8.add (phiint_9 (ε := ε))
  have hT10 : IntervalIntegrable (fun a : ℝ => ((((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT9.add (phiint_10 (ε := ε))
  have hT11 : IntervalIntegrable (fun a : ℝ => (((((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) volume (1/10) (1/2) :=
    hT10.add (phiint_11 (ε := ε))
  have hIntR := hT11
  have hmonoR : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (if a+3*b < 99/100 then (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0))
      ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), (((((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hIntF hIntR
    intro a ha
    exact hstep a ha
  have e1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT0 (phiint_1 (ε := ε))
  have e2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT1 (phiint_2 (ε := ε))
  have e3 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT2 (phiint_3 (ε := ε))
  have e4 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT3 (phiint_4 (ε := ε))
  have e5 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT4 (phiint_5 (ε := ε))
  have e6 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT5 (phiint_6 (ε := ε))
  have e7 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT6 (phiint_7 (ε := ε))
  have e8 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT7 (phiint_8 (ε := ε))
  have e9 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT8 (phiint_9 (ε := ε))
  have e10 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ((((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT9 (phiint_10 (ε := ε))
  have e11 : (∫ a in (1/10:ℝ)..(1/2:ℝ), (((((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))))
      = (∫ a in (1/10:ℝ)..(1/2:ℝ), (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) :=
    intervalIntegral.integral_add hT10 (phiint_11 (ε := ε))
  have hRval : (∫ a in (1/10:ℝ)..(1/2:ℝ), (((((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) = (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + (∫ a in (1/10:ℝ)..(1/2:ℝ), ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) := by
    rw [e11]
    rw [e10]
    rw [e9]
    rw [e8]
    rw [e7]
    rw [e6]
    rw [e5]
    rw [e4]
    rw [e3]
    rw [e2]
    rw [e1]
  have hsum : (∫ a in (1/10:ℝ)..(1/2:ℝ), (((((((((((((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((if (73017/250000:ℝ) ≤ a ∧ a ≤ (75003/200000:ℝ) then 1/a else 0) + (if (1719337/4000000:ℝ) ≤ a ∧ a ≤ (43751/100000:ℝ) then 1/a else 0) + (if (1989759/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0)) + ((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((if (135813/500000:ℝ) ≤ a ∧ a ≤ (1469397/4000000:ℝ) then 1/a else 0) + (if (844337/2000000:ℝ) ≤ a ∧ a ≤ (1739819/4000000:ℝ) then 1/a else 0) + (if (989769/2000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((if (15699/62500:ℝ) ≤ a ∧ a ≤ (719367/2000000:ℝ) then 1/a else 0) + (if (1658011/4000000:ℝ) ≤ a ∧ a ≤ (864799/2000000:ℝ) then 1/a else 0) + (if (1969317/4000000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((if (115371/500000:ℝ) ≤ a ∧ a ≤ (1408071/4000000:ℝ) then 1/a else 0) + (if (406837/1000000:ℝ) ≤ a ∧ a ≤ (1719377/4000000:ℝ) then 1/a else 0) + (if (244887/500000:ℝ) ≤ a ∧ a ≤ (1/2:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((if (2103/10000:ℝ) ≤ a ∧ a ≤ (10761/31250:ℝ) then 1/a else 0) + (if (319337/800000:ℝ) ≤ a ∧ a ≤ (427289/1000000:ℝ) then 1/a else 0) + (if (15591/32000:ℝ) ≤ a ∧ a ≤ (246189/500000:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((if (94929/500000:ℝ) ≤ a ∧ a ≤ (269349/800000:ℝ) then 1/a else 0) + (if (783011/2000000:ℝ) ≤ a ∧ a ≤ (339787/800000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((if (46579/250000:ℝ) ≤ a ∧ a ≤ (658041/2000000:ℝ) then 1/a else 0) + (if (1535359/4000000:ℝ) ≤ a ∧ a ≤ (844357/2000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((if (196537/1000000:ℝ) ≤ a ∧ a ≤ (1285419/4000000:ℝ) then 1/a else 0) + (if (188087/500000:ℝ) ≤ a ∧ a ≤ (400389/1000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((if (103379/500000:ℝ) ≤ a ∧ a ≤ (313689/1000000:ℝ) then 1/a else 0) + (if (1474033/4000000:ℝ) ≤ a ∧ a ≤ (184863/500000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((if (216979/1000000:ℝ) ≤ a ∧ a ≤ (1224093/4000000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((if (142/625:ℝ) ≤ a ∧ a ≤ (771/2500:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0))) + ((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((if (1193/5000:ℝ) ≤ a ∧ a ≤ (1371/5000:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0) + (if (0:ℝ) ≤ a ∧ a ≤ (0:ℝ) then 1/a else 0)))) ≤ (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((((75003/200000:ℝ) - (73017/250000:ℝ))/(73017/250000:ℝ) - ((75003/200000:ℝ) - (73017/250000:ℝ))^2/(2*(73017/250000:ℝ)*(75003/200000:ℝ))) + (((43751/100000:ℝ) - (1719337/4000000:ℝ))/(1719337/4000000:ℝ) - ((43751/100000:ℝ) - (1719337/4000000:ℝ))^2/(2*(1719337/4000000:ℝ)*(43751/100000:ℝ))) + (((1/2:ℝ) - (1989759/4000000:ℝ))/(1989759/4000000:ℝ) - ((1/2:ℝ) - (1989759/4000000:ℝ))^2/(2*(1989759/4000000:ℝ)*(1/2:ℝ)))) : ℝ) + (((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((((1469397/4000000:ℝ) - (135813/500000:ℝ))/(135813/500000:ℝ) - ((1469397/4000000:ℝ) - (135813/500000:ℝ))^2/(2*(135813/500000:ℝ)*(1469397/4000000:ℝ))) + (((1739819/4000000:ℝ) - (844337/2000000:ℝ))/(844337/2000000:ℝ) - ((1739819/4000000:ℝ) - (844337/2000000:ℝ))^2/(2*(844337/2000000:ℝ)*(1739819/4000000:ℝ))) + (((1/2:ℝ) - (989769/2000000:ℝ))/(989769/2000000:ℝ) - ((1/2:ℝ) - (989769/2000000:ℝ))^2/(2*(989769/2000000:ℝ)*(1/2:ℝ)))) : ℝ) + (((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((((719367/2000000:ℝ) - (15699/62500:ℝ))/(15699/62500:ℝ) - ((719367/2000000:ℝ) - (15699/62500:ℝ))^2/(2*(15699/62500:ℝ)*(719367/2000000:ℝ))) + (((864799/2000000:ℝ) - (1658011/4000000:ℝ))/(1658011/4000000:ℝ) - ((864799/2000000:ℝ) - (1658011/4000000:ℝ))^2/(2*(1658011/4000000:ℝ)*(864799/2000000:ℝ))) + (((1/2:ℝ) - (1969317/4000000:ℝ))/(1969317/4000000:ℝ) - ((1/2:ℝ) - (1969317/4000000:ℝ))^2/(2*(1969317/4000000:ℝ)*(1/2:ℝ)))) : ℝ) + (((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((((1408071/4000000:ℝ) - (115371/500000:ℝ))/(115371/500000:ℝ) - ((1408071/4000000:ℝ) - (115371/500000:ℝ))^2/(2*(115371/500000:ℝ)*(1408071/4000000:ℝ))) + (((1719377/4000000:ℝ) - (406837/1000000:ℝ))/(406837/1000000:ℝ) - ((1719377/4000000:ℝ) - (406837/1000000:ℝ))^2/(2*(406837/1000000:ℝ)*(1719377/4000000:ℝ))) + (((1/2:ℝ) - (244887/500000:ℝ))/(244887/500000:ℝ) - ((1/2:ℝ) - (244887/500000:ℝ))^2/(2*(244887/500000:ℝ)*(1/2:ℝ)))) : ℝ) + (((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((((10761/31250:ℝ) - (2103/10000:ℝ))/(2103/10000:ℝ) - ((10761/31250:ℝ) - (2103/10000:ℝ))^2/(2*(2103/10000:ℝ)*(10761/31250:ℝ))) + (((427289/1000000:ℝ) - (319337/800000:ℝ))/(319337/800000:ℝ) - ((427289/1000000:ℝ) - (319337/800000:ℝ))^2/(2*(319337/800000:ℝ)*(427289/1000000:ℝ))) + (((246189/500000:ℝ) - (15591/32000:ℝ))/(15591/32000:ℝ) - ((246189/500000:ℝ) - (15591/32000:ℝ))^2/(2*(15591/32000:ℝ)*(246189/500000:ℝ)))) : ℝ) + (((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((((269349/800000:ℝ) - (94929/500000:ℝ))/(94929/500000:ℝ) - ((269349/800000:ℝ) - (94929/500000:ℝ))^2/(2*(94929/500000:ℝ)*(269349/800000:ℝ))) + (((339787/800000:ℝ) - (783011/2000000:ℝ))/(783011/2000000:ℝ) - ((339787/800000:ℝ) - (783011/2000000:ℝ))^2/(2*(783011/2000000:ℝ)*(339787/800000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((((658041/2000000:ℝ) - (46579/250000:ℝ))/(46579/250000:ℝ) - ((658041/2000000:ℝ) - (46579/250000:ℝ))^2/(2*(46579/250000:ℝ)*(658041/2000000:ℝ))) + (((844357/2000000:ℝ) - (1535359/4000000:ℝ))/(1535359/4000000:ℝ) - ((844357/2000000:ℝ) - (1535359/4000000:ℝ))^2/(2*(1535359/4000000:ℝ)*(844357/2000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((((1285419/4000000:ℝ) - (196537/1000000:ℝ))/(196537/1000000:ℝ) - ((1285419/4000000:ℝ) - (196537/1000000:ℝ))^2/(2*(196537/1000000:ℝ)*(1285419/4000000:ℝ))) + (((400389/1000000:ℝ) - (188087/500000:ℝ))/(188087/500000:ℝ) - ((400389/1000000:ℝ) - (188087/500000:ℝ))^2/(2*(188087/500000:ℝ)*(400389/1000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((((313689/1000000:ℝ) - (103379/500000:ℝ))/(103379/500000:ℝ) - ((313689/1000000:ℝ) - (103379/500000:ℝ))^2/(2*(103379/500000:ℝ)*(313689/1000000:ℝ))) + (((184863/500000:ℝ) - (1474033/4000000:ℝ))/(1474033/4000000:ℝ) - ((184863/500000:ℝ) - (1474033/4000000:ℝ))^2/(2*(1474033/4000000:ℝ)*(184863/500000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((((1224093/4000000:ℝ) - (216979/1000000:ℝ))/(216979/1000000:ℝ) - ((1224093/4000000:ℝ) - (216979/1000000:ℝ))^2/(2*(216979/1000000:ℝ)*(1224093/4000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((((771/2500:ℝ) - (142/625:ℝ))/(142/625:ℝ) - ((771/2500:ℝ) - (142/625:ℝ))^2/(2*(142/625:ℝ)*(771/2500:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((((1371/5000:ℝ) - (1193/5000:ℝ))/(1193/5000:ℝ) - ((1371/5000:ℝ) - (1193/5000:ℝ))^2/(2*(1193/5000:ℝ)*(1371/5000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) := by
    rw [hRval]
    linarith [phibound_0 (ε := ε), phibound_1 (ε := ε), phibound_2 (ε := ε), phibound_3 (ε := ε), phibound_4 (ε := ε), phibound_5 (ε := ε), phibound_6 (ε := ε), phibound_7 (ε := ε), phibound_8 (ε := ε), phibound_9 (ε := ε), phibound_10 (ε := ε), phibound_11 (ε := ε)]
  have hCval : (((7/200) * (1/(2*(12499/100000:ℝ)^2) - 1/(2*(135211/1000000:ℝ)^2))) * ((((75003/200000:ℝ) - (73017/250000:ℝ))/(73017/250000:ℝ) - ((75003/200000:ℝ) - (73017/250000:ℝ))^2/(2*(73017/250000:ℝ)*(75003/200000:ℝ))) + (((43751/100000:ℝ) - (1719337/4000000:ℝ))/(1719337/4000000:ℝ) - ((43751/100000:ℝ) - (1719337/4000000:ℝ))^2/(2*(1719337/4000000:ℝ)*(43751/100000:ℝ))) + (((1/2:ℝ) - (1989759/4000000:ℝ))/(1989759/4000000:ℝ) - ((1/2:ℝ) - (1989759/4000000:ℝ))^2/(2*(1989759/4000000:ℝ)*(1/2:ℝ)))) : ℝ) + (((7/200) * (1/(2*(135211/1000000:ℝ)^2) - 1/(2*(18179/125000:ℝ)^2))) * ((((1469397/4000000:ℝ) - (135813/500000:ℝ))/(135813/500000:ℝ) - ((1469397/4000000:ℝ) - (135813/500000:ℝ))^2/(2*(135813/500000:ℝ)*(1469397/4000000:ℝ))) + (((1739819/4000000:ℝ) - (844337/2000000:ℝ))/(844337/2000000:ℝ) - ((1739819/4000000:ℝ) - (844337/2000000:ℝ))^2/(2*(844337/2000000:ℝ)*(1739819/4000000:ℝ))) + (((1/2:ℝ) - (989769/2000000:ℝ))/(989769/2000000:ℝ) - ((1/2:ℝ) - (989769/2000000:ℝ))^2/(2*(989769/2000000:ℝ)*(1/2:ℝ)))) : ℝ) + (((7/200) * (1/(2*(18179/125000:ℝ)^2) - 1/(2*(155653/1000000:ℝ)^2))) * ((((719367/2000000:ℝ) - (15699/62500:ℝ))/(15699/62500:ℝ) - ((719367/2000000:ℝ) - (15699/62500:ℝ))^2/(2*(15699/62500:ℝ)*(719367/2000000:ℝ))) + (((864799/2000000:ℝ) - (1658011/4000000:ℝ))/(1658011/4000000:ℝ) - ((864799/2000000:ℝ) - (1658011/4000000:ℝ))^2/(2*(1658011/4000000:ℝ)*(864799/2000000:ℝ))) + (((1/2:ℝ) - (1969317/4000000:ℝ))/(1969317/4000000:ℝ) - ((1/2:ℝ) - (1969317/4000000:ℝ))^2/(2*(1969317/4000000:ℝ)*(1/2:ℝ)))) : ℝ) + (((7/200) * (1/(2*(155653/1000000:ℝ)^2) - 1/(2*(82937/500000:ℝ)^2))) * ((((1408071/4000000:ℝ) - (115371/500000:ℝ))/(115371/500000:ℝ) - ((1408071/4000000:ℝ) - (115371/500000:ℝ))^2/(2*(115371/500000:ℝ)*(1408071/4000000:ℝ))) + (((1719377/4000000:ℝ) - (406837/1000000:ℝ))/(406837/1000000:ℝ) - ((1719377/4000000:ℝ) - (406837/1000000:ℝ))^2/(2*(406837/1000000:ℝ)*(1719377/4000000:ℝ))) + (((1/2:ℝ) - (244887/500000:ℝ))/(244887/500000:ℝ) - ((1/2:ℝ) - (244887/500000:ℝ))^2/(2*(244887/500000:ℝ)*(1/2:ℝ)))) : ℝ) + (((7/200) * (1/(2*(82937/500000:ℝ)^2) - 1/(2*(35219/200000:ℝ)^2))) * ((((10761/31250:ℝ) - (2103/10000:ℝ))/(2103/10000:ℝ) - ((10761/31250:ℝ) - (2103/10000:ℝ))^2/(2*(2103/10000:ℝ)*(10761/31250:ℝ))) + (((427289/1000000:ℝ) - (319337/800000:ℝ))/(319337/800000:ℝ) - ((427289/1000000:ℝ) - (319337/800000:ℝ))^2/(2*(319337/800000:ℝ)*(427289/1000000:ℝ))) + (((246189/500000:ℝ) - (15591/32000:ℝ))/(15591/32000:ℝ) - ((246189/500000:ℝ) - (15591/32000:ℝ))^2/(2*(15591/32000:ℝ)*(246189/500000:ℝ)))) : ℝ) + (((7/200) * (1/(2*(35219/200000:ℝ)^2) - 1/(2*(46579/250000:ℝ)^2))) * ((((269349/800000:ℝ) - (94929/500000:ℝ))/(94929/500000:ℝ) - ((269349/800000:ℝ) - (94929/500000:ℝ))^2/(2*(94929/500000:ℝ)*(269349/800000:ℝ))) + (((339787/800000:ℝ) - (783011/2000000:ℝ))/(783011/2000000:ℝ) - ((339787/800000:ℝ) - (783011/2000000:ℝ))^2/(2*(783011/2000000:ℝ)*(339787/800000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(46579/250000:ℝ)^2) - 1/(2*(196537/1000000:ℝ)^2))) * ((((658041/2000000:ℝ) - (46579/250000:ℝ))/(46579/250000:ℝ) - ((658041/2000000:ℝ) - (46579/250000:ℝ))^2/(2*(46579/250000:ℝ)*(658041/2000000:ℝ))) + (((844357/2000000:ℝ) - (1535359/4000000:ℝ))/(1535359/4000000:ℝ) - ((844357/2000000:ℝ) - (1535359/4000000:ℝ))^2/(2*(1535359/4000000:ℝ)*(844357/2000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(196537/1000000:ℝ)^2) - 1/(2*(103379/500000:ℝ)^2))) * ((((1285419/4000000:ℝ) - (196537/1000000:ℝ))/(196537/1000000:ℝ) - ((1285419/4000000:ℝ) - (196537/1000000:ℝ))^2/(2*(196537/1000000:ℝ)*(1285419/4000000:ℝ))) + (((400389/1000000:ℝ) - (188087/500000:ℝ))/(188087/500000:ℝ) - ((400389/1000000:ℝ) - (188087/500000:ℝ))^2/(2*(188087/500000:ℝ)*(400389/1000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(103379/500000:ℝ)^2) - 1/(2*(216979/1000000:ℝ)^2))) * ((((313689/1000000:ℝ) - (103379/500000:ℝ))/(103379/500000:ℝ) - ((313689/1000000:ℝ) - (103379/500000:ℝ))^2/(2*(103379/500000:ℝ)*(313689/1000000:ℝ))) + (((184863/500000:ℝ) - (1474033/4000000:ℝ))/(1474033/4000000:ℝ) - ((184863/500000:ℝ) - (1474033/4000000:ℝ))^2/(2*(1474033/4000000:ℝ)*(184863/500000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(216979/1000000:ℝ)^2) - 1/(2*(142/625:ℝ)^2))) * ((((1224093/4000000:ℝ) - (216979/1000000:ℝ))/(216979/1000000:ℝ) - ((1224093/4000000:ℝ) - (216979/1000000:ℝ))^2/(2*(216979/1000000:ℝ)*(1224093/4000000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(142/625:ℝ)^2) - 1/(2*(1193/5000:ℝ)^2))) * ((((771/2500:ℝ) - (142/625:ℝ))/(142/625:ℝ) - ((771/2500:ℝ) - (142/625:ℝ))^2/(2*(142/625:ℝ)*(771/2500:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) + (((7/200) * (1/(2*(1193/5000:ℝ)^2) - 1/(2*(1/4:ℝ)^2))) * ((((1371/5000:ℝ) - (1193/5000:ℝ))/(1193/5000:ℝ) - ((1371/5000:ℝ) - (1193/5000:ℝ))^2/(2*(1193/5000:ℝ)*(1371/5000:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ))) + (((0:ℝ) - (0:ℝ))/(0:ℝ) - ((0:ℝ) - (0:ℝ))^2/(2*(0:ℝ)*(0:ℝ)))) : ℝ) ≤ 2/5 := by norm_num
  linarith [hmonoR, hsum, hCval]

/-- The target of the split: the integral over the box of the majorant of the upward variation
of the discarded lower coefficient integrand is at most two. The three branch functions of
`integrand_eq_pieces` are separately measurable and bounded by `10^4`, so the double integral
splits, and the three leaf bounds add up to two. -/
theorem leaf_two_variation_quadrature_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0)) ≤ 2 := by
  let f1 : ℝ → ℝ → ℝ := fun a b =>
    if 1 ≤ a+3*b then
      (if lowerTwoDiscarded ε a b then 1/(a*b*(99/100-a-b)*(1-a-b)) else 0) else 0
  let f2 : ℝ → ℝ → ℝ := fun a b =>
    if ¬(1 ≤ a+3*b) ∧ (99/100:ℝ) ≤ a+3*b then
      (if lowerTwoDiscarded ε a b then (107/200)/(a*b^3) else 0) else 0
  let f3 : ℝ → ℝ → ℝ := fun a b =>
    if a+3*b < (99/100:ℝ) then
      (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0
  have hAset : MeasurableSet {p : ℝ × ℝ | (1:ℝ) ≤ p.1+3*p.2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hBset : MeasurableSet {p : ℝ × ℝ | (99/100:ℝ) ≤ p.1+3*p.2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hCset : MeasurableSet {p : ℝ × ℝ | p.1+3*p.2 < (99/100:ℝ)} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hABset : MeasurableSet {p : ℝ × ℝ | ¬(1 ≤ p.1+3*p.2) ∧ (99/100:ℝ) ≤ p.1+3*p.2} := by
    rw [Set.ofPred_and]
    exact hAset.compl.inter hBset
  have hf1 : Measurable (fun p : ℝ × ℝ => f1 p.1 p.2) :=
    Measurable.ite hAset
      (Measurable.ite (two_density_region_measurable ε) (by fun_prop) measurable_const)
      measurable_const
  have hf2 : Measurable (fun p : ℝ × ℝ => f2 p.1 p.2) :=
    Measurable.ite hABset
      (Measurable.ite (two_density_region_measurable ε) (by fun_prop) measurable_const)
      measurable_const
  have hf3 : Measurable (fun p : ℝ × ℝ => f3 p.1 p.2) :=
    Measurable.ite hCset
      (Measurable.ite (two_density_region_measurable ε) (by fun_prop) measurable_const)
      measurable_const
  have hM1 : ∀ a b, |f1 a b| ≤ 10^4 := by
    intro a b
    have h := piece_high_bound hε8 a b
    rw [abs_of_nonneg h.1]
    exact h.2
  have hM2 : ∀ a b, |f2 a b| ≤ 10^4 := by
    intro a b
    have h := piece_middle_bound hε8 a b
    rw [abs_of_nonneg h.1]
    exact h.2
  have hM3 : ∀ a b, |f3 a b| ≤ 10^4 := by
    intro a b
    have h := piece_low_bound hε8 a b
    rw [abs_of_nonneg h.1]
    exact h.2
  have hi1 : ∀ a, IntervalIntegrable (fun b => f1 a b) volume (1/10) (1/2) :=
    fun a => slope_level_integrable f1 hf1 hM1 (1/10) (1/2) a
  have hi2 : ∀ a, IntervalIntegrable (fun b => f2 a b) volume (1/10) (1/2) :=
    fun a => slope_level_integrable f2 hf2 hM2 (1/10) (1/2) a
  have hi3 : ∀ a, IntervalIntegrable (fun b => f3 a b) volume (1/10) (1/2) :=
    fun a => slope_level_integrable f3 hf3 hM3 (1/10) (1/2) a
  have hl1 := four_density_level f1 hf1 hM1 (1/10) (1/2)
  have hl2 := four_density_level f2 hf2 hM2 (1/10) (1/2)
  have hl3 := four_density_level f3 hf3 hM3 (1/10) (1/2)
  have ho1 : IntervalIntegrable (fun a => ∫ b in (1/10:ℝ)..(1/2:ℝ), f1 a b) volume (1/10) (1/2) :=
    slope_level_integrable (fun (_ : Unit) a => ∫ b in (1/10:ℝ)..(1/2:ℝ), f1 a b)
      (hl1.1.comp measurable_snd) (fun _ a => hl1.2 a) (1/10) (1/2) ()
  have ho2 : IntervalIntegrable (fun a => ∫ b in (1/10:ℝ)..(1/2:ℝ), f2 a b) volume (1/10) (1/2) :=
    slope_level_integrable (fun (_ : Unit) a => ∫ b in (1/10:ℝ)..(1/2:ℝ), f2 a b)
      (hl2.1.comp measurable_snd) (fun _ a => hl2.2 a) (1/10) (1/2) ()
  have ho3 : IntervalIntegrable (fun a => ∫ b in (1/10:ℝ)..(1/2:ℝ), f3 a b) volume (1/10) (1/2) :=
    slope_level_integrable (fun (_ : Unit) a => ∫ b in (1/10:ℝ)..(1/2:ℝ), f3 a b)
      (hl3.1.comp measurable_snd) (fun _ a => hl3.2 a) (1/10) (1/2) ()
  have hin : ∀ a, (∫ b in (1/10:ℝ)..(1/2:ℝ), (f1 a b + f2 a b + f3 a b)) =
      (∫ b in (1/10:ℝ)..(1/2:ℝ), f1 a b) + (∫ b in (1/10:ℝ)..(1/2:ℝ), f2 a b) +
        ∫ b in (1/10:ℝ)..(1/2:ℝ), f3 a b := fun a =>
    (intervalIntegral.integral_add ((hi1 a).add (hi2 a)) (hi3 a)).trans
      (congrArg (fun t => t + ∫ b in (1/10:ℝ)..(1/2:ℝ), f3 a b)
        (intervalIntegral.integral_add (hi1 a) (hi2 a)))
  have hcongr : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0)) =
      ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (f1 a b + f2 a b + f3 a b) := by
    apply intervalIntegral.integral_congr
    intro a _
    apply intervalIntegral.integral_congr
    intro b _
    exact integrand_eq_pieces a b
  have hsplit : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), (f1 a b + f2 a b + f3 a b)) =
      (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), f1 a b) +
        (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), f2 a b) +
        ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), f3 a b := by
    simp only [hin]
    rw [intervalIntegral.integral_add (ho1.add ho2) ho3]
    rw [intervalIntegral.integral_add ho1 ho2]
  have hq1 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), f1 a b) ≤ 3/2 :=
    leaf_variation_high_integral hε hε8
  have hq2 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), f2 a b) ≤ 1/10 :=
    leaf_variation_middle_integral hε hε8
  have hq3 : (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ), f3 a b) ≤ 2/5 :=
    leaf_variation_low_integral hε hε8
  rw [hcongr, hsplit]
  linarith

end LeanLab.BHP1997.LowerShortC165

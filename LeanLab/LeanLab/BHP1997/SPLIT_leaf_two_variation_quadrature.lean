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

/-- LEAF: the branch of the majorant taken when `a + 3 b < 99/100`, integrated over the box,
is at most `2/5`. A quadrature gives about 0.14. -/
theorem leaf_variation_low_integral {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if a+3*b < (99/100:ℝ) then
        (if lowerTwoDiscarded ε a b then (7/200)/(a*b^3) else 0) else 0)) ≤ 2/5 := by
  sorry

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

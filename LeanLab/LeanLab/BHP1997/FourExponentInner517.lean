/-
P0069, Section 5, page 51, display 5.17.
The inner integrated E4 kernels and their measurable bounded sections.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentOuterVariation517

namespace LeanLab.BHP1997.LowerShortC165
open Classical MeasureTheory Decomp514a DecompC165d
open scoped BigOperators

/-- Page 51 display 5.17. The E4 kernel after integrating its last exponent. -/
noncomputable def fourExponentInnerOne (ω : ℝ → ℝ) (ε s a b c : ℝ) : ℝ :=
  ∫ d in lowerFourGridReal 0..lowerFourGridReal 128, fourExponentKernel ω ε s a b c d

/-- Page 51 display 5.17. The E4 kernel after integrating its last two exponents. -/
noncomputable def fourExponentInnerTwo (ω : ℝ → ℝ) (ε s a b : ℝ) : ℝ :=
  ∫ c in lowerFourGridReal 0..lowerFourGridReal 128, fourExponentInnerOne ω ε s a b c

/-- Page 51 display 5.17. The E4 kernel after integrating its last three exponents. -/
noncomputable def fourExponentInnerThree (ω : ℝ → ℝ) (ε s a : ℝ) : ℝ :=
  ∫ b in lowerFourGridReal 0..lowerFourGridReal 128, fourExponentInnerTwo ω ε s a b

/-- Page 51 display 5.17. A globally bounded measurable section is
integrable on every bounded exponent interval. -/
theorem four_exponent_bounded_integrable (f : ℝ → ℝ) (hm : Measurable f)
    (hf : ∀ x, |f x| ≤ (10 : ℝ)^5) (l r : ℝ) : IntervalIntegrable f volume l r := by
  have hi : ∀ u v : ℝ, IntegrableOn f (Set.Ioc u v) := by
    intro u v
    refine Measure.integrableOn_of_bounded (M := (10 : ℝ)^5)
      measure_Ioc_lt_top.ne hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    simpa only [Real.norm_eq_abs] using hf x
  exact ⟨hi l r, hi r l⟩

/-- Page 51 display 5.17. The first inner integral is jointly measurable
and bounded by the original uniform kernel bound. -/
theorem four_exponent_inner_one_props {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s : ℝ) :
    Measurable (fun p : (ℝ×ℝ)×ℝ => fourExponentInnerOne ω ε s p.1.1 p.1.2 p.2) ∧
      ∀ a b c, |fourExponentInnerOne ω ε s a b c| ≤ (10 : ℝ)^5 := by
  have hm : Measurable (fun p : ((ℝ×ℝ)×ℝ)×ℝ =>
      fourExponentKernel ω ε s p.1.1.1 p.1.1.2 p.1.2 p.2) := by
    simpa only [fourExponentKernel] using four_density_integrand_measurable hω hz ε s
  have hb : ∀ (p : (ℝ×ℝ)×ℝ) d,
      |fourExponentKernel ω ε s p.1.1 p.1.2 p.2 d| ≤ (10 : ℝ)^5 := fun p d => by
    simpa only [fourExponentKernel] using four_density_integrand_bound hω hz hε hε8 s p.1.1 p.1.2 p.2 d
  obtain ⟨h1, h2⟩ := four_density_level
    (fun (p : (ℝ×ℝ)×ℝ) d => fourExponentKernel ω ε s p.1.1 p.1.2 p.2 d) hm hb
    (lowerFourGridReal 0) (lowerFourGridReal 128)
  refine ⟨by simpa only [fourExponentInnerOne] using h1, fun a b c => ?_⟩
  have h := h2 ((a,b),c)
  have hlen : |lowerFourGridReal 128-lowerFourGridReal 0| ≤ 1 := by
    norm_num [lowerFourGridReal, lowerFourGridPoint]
  exact h.trans (by nlinarith)

/-- Page 51 display 5.17. The second inner integral is jointly measurable
and bounded by the original uniform kernel bound. -/
theorem four_exponent_inner_two_props {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s : ℝ) :
    Measurable (fun p : ℝ×ℝ => fourExponentInnerTwo ω ε s p.1 p.2) ∧
      ∀ a b, |fourExponentInnerTwo ω ε s a b| ≤ (10 : ℝ)^5 := by
  obtain ⟨hm, hb⟩ := four_exponent_inner_one_props hω hz hε hε8 s
  obtain ⟨h1, h2⟩ := four_density_level
    (fun (p : ℝ×ℝ) c => fourExponentInnerOne ω ε s p.1 p.2 c) hm
    (fun p c => hb p.1 p.2 c) (lowerFourGridReal 0) (lowerFourGridReal 128)
  refine ⟨by simpa only [fourExponentInnerTwo] using h1, fun a b => ?_⟩
  have h := h2 (a,b)
  have hlen : |lowerFourGridReal 128-lowerFourGridReal 0| ≤ 1 := by
    norm_num [lowerFourGridReal, lowerFourGridPoint]
  exact h.trans (by nlinarith)

/-- Page 51 display 5.17. The third inner integral is measurable and
bounded by the original uniform kernel bound. -/
theorem four_exponent_inner_three_props {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s : ℝ) :
    Measurable (fourExponentInnerThree ω ε s) ∧
      ∀ a, |fourExponentInnerThree ω ε s a| ≤ (10 : ℝ)^5 := by
  obtain ⟨hm, hb⟩ := four_exponent_inner_two_props hω hz hε hε8 s
  obtain ⟨h1, h2⟩ := four_density_level (fourExponentInnerTwo ω ε s) hm hb
    (lowerFourGridReal 0) (lowerFourGridReal 128)
  refine ⟨?_, fun a => ?_⟩
  · change Measurable (fun a => fourExponentInnerThree ω ε s a)
    simpa only [fourExponentInnerThree] using h1
  · have h := h2 a
    have hlen : |lowerFourGridReal 128-lowerFourGridReal 0| ≤ 1 := by
      norm_num [lowerFourGridReal, lowerFourGridPoint]
    exact h.trans (by nlinarith)

/-- Page 51 display 5.17. Every last section of the first inner integral
is interval integrable. -/
theorem four_exponent_inner_one_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b l r : ℝ) :
    IntervalIntegrable (fourExponentInnerOne ω ε s a b) volume l r := by
  obtain ⟨hm, hb⟩ := four_exponent_inner_one_props hω hz hε hε8 s
  have hmeas : Measurable (fourExponentInnerOne ω ε s a b) := by
    change Measurable (fun c => fourExponentInnerOne ω ε s a b c)
    exact hm.comp (by fun_prop : Measurable (fun c : ℝ => ((a,b),c)))
  exact four_exponent_bounded_integrable _ hmeas (hb a b) l r

/-- Page 51 display 5.17. Every last section of the second inner integral
is interval integrable. -/
theorem four_exponent_inner_two_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a l r : ℝ) :
    IntervalIntegrable (fourExponentInnerTwo ω ε s a) volume l r := by
  obtain ⟨hm, hb⟩ := four_exponent_inner_two_props hω hz hε hε8 s
  have hmeas : Measurable (fourExponentInnerTwo ω ε s a) := by
    change Measurable (fun b => fourExponentInnerTwo ω ε s a b)
    exact hm.comp (by fun_prop : Measurable (fun b : ℝ => (a,b)))
  exact four_exponent_bounded_integrable _ hmeas (hb a) l r

/-- Page 51 display 5.17. The third inner integral is interval integrable. -/
theorem four_exponent_inner_three_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s l r : ℝ) :
    IntervalIntegrable (fourExponentInnerThree ω ε s) volume l r := by
  obtain ⟨hm, hb⟩ := four_exponent_inner_three_props hω hz hε hε8 s
  exact four_exponent_bounded_integrable _ hm hb l r

#print axioms four_exponent_bounded_integrable
#print axioms four_exponent_inner_one_props
#print axioms four_exponent_inner_two_props
#print axioms four_exponent_inner_three_props
#print axioms four_exponent_inner_one_integrable
#print axioms four_exponent_inner_two_integrable
#print axioms four_exponent_inner_three_integrable
end LeanLab.BHP1997.LowerShortC165

/-
P0069, Section 5, page 51, display 5.17.
The last exponent fibre has uniformly bounded variation.
The region contributes at most 600 jumps. The Buchstab cutoff adds one.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentKernel517
import LeanLab.BHP1997.FourDensityMain517b
import Mathlib.Topology.EMetricSpace.BoundedVariation

namespace LeanLab.BHP1997.LowerShortC165
open Classical Decomp514a MeasureTheory
open scoped BigOperators

/-- Page 51 display 5.17. On E4 the nonzero Buchstab cutoff is a linear
inequality in the last exponent. -/
theorem four_exponent_kernel_active {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (ω : ℝ → ℝ) (s a b c d : ℝ) :
    fourExponentKernel ω ε s a b c d =
      if lowerFourRegion ε a b c d ∧ 2*d ≤ s-a-b-c then
        ω ((s-a-b-c-d)/d)/(a*b*c*d^2) else 0 := by
  by_cases hr : lowerFourRegion ε a b c d
  · have hd := (four_density_region_box hε hε8 hr).1
    have hd0 : 0 < d := by linarith
    have heq : ((s-a-b-c-d)/d < 1) ↔ ¬ 2*d ≤ s-a-b-c := by
      rw [div_lt_iff₀ hd0]
      constructor <;> intro h <;> linarith
    simp only [fourExponentKernel, if_pos hr, hr, true_and, heq]
    by_cases h : 2*d ≤ s-a-b-c <;> simp [h]
  · simp [fourExponentKernel, hr]

/-- Page 51 display 5.17. The active E4 indicator changes at most 601 times
on a monotone last coordinate fibre. -/
theorem four_exponent_active_jumps_d (ε s a b c : ℝ) (e : ℕ → ℝ)
    (he : Monotone e) (lo hi : ℕ) :
    ∑ i ∈ Finset.Ico lo hi,
      |(if lowerFourRegion ε a b c (e (i+1)) ∧ 2*e (i+1) ≤ s-a-b-c then (1 : ℝ) else 0) -
        (if lowerFourRegion ε a b c (e i) ∧ 2*e i ≤ s-a-b-c then (1 : ℝ) else 0)| ≤ 601 := by
  have hr := four_region_jumps ε e he a 0 b 0 c 0 0 1 lo hi
  simp only [zero_mul, add_zero, one_mul, zero_add] at hr
  have hc := four_atom_jump he (fun n => 2*e n) (fun _ => s-a-b-c)
    (-2) (s-a-b-c) (fun n => by ring) lo hi
  exact (indicator_variation_and_le (fun n => lowerFourRegion ε a b c (e n))
    (fun n => 2*e n ≤ s-a-b-c) (Finset.Ico lo hi)).trans (by linarith)

/-- Page 51 display 5.17. One step of the actual kernel variation is the
smooth last coordinate change plus the cost of an active indicator jump. -/
theorem four_exponent_kernel_step_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s a b c u v : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |fourExponentKernel ω ε s a b c v - fourExponentKernel ω ε s a b c u| ≤
      60000000 * |v-u| + 10^5 *
        |(if lowerFourRegion ε a b c v ∧ 2*v ≤ s-a-b-c then (1 : ℝ) else 0) -
          (if lowerFourRegion ε a b c u ∧ 2*u ≤ s-a-b-c then (1 : ℝ) else 0)| := by
  have hM : ∀ d : ℝ, |fourExponentKernel ω ε s a b c d| ≤ 10^5 := fun d => by
    simpa only [fourExponentKernel] using four_density_integrand_bound hω hz hε hε8 s a b c d
  have heq := four_exponent_kernel_active hε hε8 ω s a b c
  by_cases hv : lowerFourRegion ε a b c v ∧ 2*v ≤ s-a-b-c
  · by_cases hu : lowerFourRegion ε a b c u ∧ 2*u ≤ s-a-b-c
    · have hdv := (four_density_region_box hε hε8 hv.1).1
      have hdu := (four_density_region_box hε hε8 hu.1).1
      have hv0 : 0 < v := by linarith
      have hu0 : 0 < u := by linarith
      have hvarg : 1 ≤ (s-a-b-c-v)/v := (le_div_iff₀ hv0).mpr (by linarith [hv.2])
      have huarg : 1 ≤ (s-a-b-c-u)/u := (le_div_iff₀ hu0).mpr (by linarith [hu.2])
      simpa only [if_pos hv, if_pos hu, sub_self, abs_zero, mul_zero, add_zero] using
        four_exponent_kernel_coordinate_d hω hz hε hε8 hs0 hs1 hv.1 hu.1 hvarg huarg
    · have hzero : fourExponentKernel ω ε s a b c u = 0 := by rw [heq u, if_neg hu]
      rw [hzero, sub_zero, if_pos hv, if_neg hu]
      norm_num
      nlinarith [hM v, abs_nonneg (v-u)]
  · have hzero : fourExponentKernel ω ε s a b c v = 0 := by rw [heq v, if_neg hv]
    by_cases hu : lowerFourRegion ε a b c u ∧ 2*u ≤ s-a-b-c
    · rw [hzero, zero_sub, abs_neg, if_neg hv, if_pos hu]
      norm_num
      nlinarith [hM u, abs_nonneg (v-u)]
    · have hzero' : fourExponentKernel ω ε s a b c u = 0 := by rw [heq u, if_neg hu]
      rw [hzero, hzero', if_neg hv, if_neg hu]
      simp only [sub_self, abs_zero, mul_zero, add_zero]
      positivity

/-- Page 51 display 5.17. The kernel variation on an arbitrary monotone
last coordinate partition is bounded by its length and 601 jumps. -/
theorem four_exponent_kernel_variation_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (a b c : ℝ) (e : ℕ → ℝ) (he : Monotone e) {lo hi : ℕ} (hlo : lo ≤ hi) :
    ∑ i ∈ Finset.Ico lo hi,
      |fourExponentKernel ω ε s a b c (e (i+1)) - fourExponentKernel ω ε s a b c (e i)| ≤
        60000000 * (e hi - e lo) + 60100000 := by
  calc _ ≤ ∑ i ∈ Finset.Ico lo hi, (60000000 * |e (i+1)-e i| + 10^5 *
        |(if lowerFourRegion ε a b c (e (i+1)) ∧ 2*e (i+1) ≤ s-a-b-c then (1 : ℝ) else 0) -
          (if lowerFourRegion ε a b c (e i) ∧ 2*e i ≤ s-a-b-c then (1 : ℝ) else 0)|) :=
        Finset.sum_le_sum (fun i _ => four_exponent_kernel_step_d hω hz hε hε8 hs0 hs1)
    _ = 60000000 * (e hi-e lo) + 10^5 * (∑ i ∈ Finset.Ico lo hi,
        |(if lowerFourRegion ε a b c (e (i+1)) ∧ 2*e (i+1) ≤ s-a-b-c then (1 : ℝ) else 0) -
          (if lowerFourRegion ε a b c (e i) ∧ 2*e i ≤ s-a-b-c then (1 : ℝ) else 0)|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      congr 1
      have habs : ∀ i : ℕ, |e (i+1)-e i| = e (i+1)-e i := fun i =>
        abs_of_nonneg (sub_nonneg.mpr (he (Nat.le_add_right i 1)))
      simp only [habs]
      exact Finset.sum_Ico_sub (f := e) hlo
    _ ≤ _ := by
      have h := four_exponent_active_jumps_d ε s a b c e he lo hi
      linarith

/-- Page 51 display 5.17. The last coordinate E4 fibre has an explicit
Mathlib extended variation bound on every compact interval. -/
theorem four_exponent_kernel_evariation_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (a b c l r : ℝ) (hlr : l ≤ r) :
    eVariationOn (fourExponentKernel ω ε s a b c) (Set.Icc l r) ≤
      ENNReal.ofReal (60000000 * (r-l) + 60100000) := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, e, he, hmem⟩
  have hv := four_exponent_kernel_variation_d hω hz hε hε8 hs0 hs1 a b c e he (Nat.zero_le n)
  have hlength : e n - e 0 ≤ r-l := by
    have h1 := (hmem n).2
    have h0 := (hmem 0).1
    linarith
  have hreal : (∑ i ∈ Finset.range n,
      |fourExponentKernel ω ε s a b c (e (i+1)) - fourExponentKernel ω ε s a b c (e i)|) ≤
      60000000 * (r-l) + 60100000 := by
    have h := hv.trans (by linarith :
      60000000 * (e n-e 0) + 60100000 ≤ 60000000 * (r-l) + 60100000)
    simpa only [Nat.Ico_zero_eq_range] using h
  simp only [edist_dist, Real.dist_eq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Page 51 display 5.17. The actual last coordinate E4 kernel has bounded
variation on every compact interval, including the region and Buchstab jumps. -/
theorem four_exponent_kernel_bounded_variation_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (a b c l r : ℝ) (hlr : l ≤ r) :
    BoundedVariationOn (fourExponentKernel ω ε s a b c) (Set.Icc l r) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (four_exponent_kernel_evariation_d hω hz hε hε8 hs0 hs1 a b c l r hlr)

/-- Page 51 display 5.17. The actual last coordinate kernel is integrable
on every bounded interval, including its region and Buchstab jumps. -/
theorem four_exponent_kernel_integrable_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b c l r : ℝ) :
    IntervalIntegrable (fourExponentKernel ω ε s a b c) MeasureTheory.volume l r := by
  have hm : Measurable (fourExponentKernel ω ε s a b c) := by
    change Measurable (fun d : ℝ => fourExponentKernel ω ε s a b c d)
    simpa only [fourExponentKernel, Function.comp_def] using
      (four_density_integrand_measurable hω hz ε s).comp
        (show Measurable (fun d : ℝ => (((a,b),c),d)) by fun_prop)
  have hi : ∀ u v : ℝ, MeasureTheory.IntegrableOn
      (fourExponentKernel ω ε s a b c) (Set.Ioc u v) := by
    intro u v
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := (10 : ℝ)^5)
      measure_Ioc_lt_top.ne hm.aestronglyMeasurable (Filter.Eventually.of_forall fun d => ?_)
    rw [Real.norm_eq_abs]
    simpa only [fourExponentKernel] using four_density_integrand_bound hω hz hε hε8 s a b c d
  exact ⟨hi l r, hi r l⟩

#print axioms four_exponent_kernel_active
#print axioms four_exponent_active_jumps_d
#print axioms four_exponent_kernel_step_d
#print axioms four_exponent_kernel_variation_d
#print axioms four_exponent_kernel_evariation_d
#print axioms four_exponent_kernel_bounded_variation_d
#print axioms four_exponent_kernel_integrable_d
end LeanLab.BHP1997.LowerShortC165

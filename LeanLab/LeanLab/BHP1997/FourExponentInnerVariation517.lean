/-
P0069, Section 5, page 51, display 5.17.
The inner integrated E4 kernels have uniform bounded variation.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentInner517

namespace LeanLab.BHP1997.LowerShortC165
open Classical MeasureTheory DecompC165d
open scoped BigOperators

/-- Page 51 display 5.17. Integrating d preserves a uniform variation
bound for the remaining c coordinate. -/
theorem four_exponent_inner_one_variation {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b : ℝ) :
    eVariationOn (fourExponentInnerOne ω ε s a b) (Set.Icc 0 1) ≤ ENNReal.ofReal 120100000 := by
  apply four_exponent_evariation_of_partition_bound
  intro z hm hmem n
  have hlen : lowerFourGridReal 128-lowerFourGridReal 0 ≤ 1 := by
    norm_num [lowerFourGridReal, lowerFourGridPoint]
  have hlr : lowerFourGridReal 0 ≤ lowerFourGridReal 128 := by
    norm_num [lowerFourGridReal, lowerFourGridPoint]
  have hwidth : z n-z 0 ≤ 1 := by
    have h0 := (hmem 0).1
    have hn := (hmem n).2
    linarith
  have hp : ∀ d : ℝ, (∑ i ∈ Finset.range n,
      |fourExponentKernel ω ε s a b (z (i+1)) d-fourExponentKernel ω ε s a b (z i) d|) ≤ 62100000 := by
    intro d
    have h := four_exponent_kernel_variation_c hω hz hε hε8 s a b d z hm (Nat.zero_le n)
    have h' := h.trans (by linarith : 2000000*(z n-z 0)+60100000 ≤ 62100000)
    simpa only [Nat.Ico_zero_eq_range] using h'
  have h := four_exponent_integral_partition_variation
    (fun c d => fourExponentKernel ω ε s a b c d) z (Finset.range n) hlr
    (fun c => four_exponent_kernel_integrable_d hω hz hε hε8 s a b c _ _)
    (fun d _ => hp d)
  change (∑ i ∈ Finset.range n,
    |fourExponentInnerOne ω ε s a b (z (i+1))-fourExponentInnerOne ω ε s a b (z i)|) ≤ _
  have h' : (∑ i ∈ Finset.range n,
      |fourExponentInnerOne ω ε s a b (z (i+1))-fourExponentInnerOne ω ε s a b (z i)|) ≤
      62100000*(lowerFourGridReal 128-lowerFourGridReal 0) := h
  nlinarith

/-- Page 51 display 5.17. Integrating c and d preserves a uniform variation
bound for the remaining b coordinate. -/
theorem four_exponent_inner_two_variation {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a : ℝ) :
    eVariationOn (fourExponentInnerTwo ω ε s a) (Set.Icc 0 1) ≤ ENNReal.ofReal 120100000 := by
  apply four_exponent_evariation_of_partition_bound
  intro z hm hmem n
  have hlen : lowerFourGridReal 128-lowerFourGridReal 0 ≤ 1 := by
    norm_num [lowerFourGridReal, lowerFourGridPoint]
  have hlr : lowerFourGridReal 0 ≤ lowerFourGridReal 128 := by
    norm_num [lowerFourGridReal, lowerFourGridPoint]
  have hwidth : z n-z 0 ≤ 1 := by
    have h0 := (hmem 0).1
    have hn := (hmem n).2
    linarith
  have shrink : ∀ T : ℝ, T ≤ 62100000*(lowerFourGridReal 128-lowerFourGridReal 0) → T ≤ 62100000 := by
    intro T hT
    nlinarith
  have hp : ∀ c d : ℝ, (∑ i ∈ Finset.range n,
      |fourExponentKernel ω ε s a (z (i+1)) c d-fourExponentKernel ω ε s a (z i) c d|) ≤ 62100000 := by
    intro c d
    have h := four_exponent_kernel_variation_b hω hz hε hε8 s a c d z hm (Nat.zero_le n)
    simpa only [Nat.Ico_zero_eq_range] using
      h.trans (by linarith : 2000000*(z n-z 0)+60100000 ≤ 62100000)
  have hp1 : ∀ c : ℝ, (∑ i ∈ Finset.range n,
      |fourExponentInnerOne ω ε s a (z (i+1)) c-fourExponentInnerOne ω ε s a (z i) c|) ≤ 62100000 := by
    intro c
    apply shrink
    exact four_exponent_integral_partition_variation
      (fun b d => fourExponentKernel ω ε s a b c d) z (Finset.range n) hlr
      (fun b => four_exponent_kernel_integrable_d hω hz hε hε8 s a b c _ _) (fun d _ => hp c d)
  have h := four_exponent_integral_partition_variation
    (fun b c => fourExponentInnerOne ω ε s a b c) z (Finset.range n) hlr
    (fun b => four_exponent_inner_one_integrable hω hz hε hε8 s a b _ _) (fun c _ => hp1 c)
  have h' : (∑ i ∈ Finset.range n,
      |fourExponentInnerTwo ω ε s a (z (i+1))-fourExponentInnerTwo ω ε s a (z i)|) ≤
      62100000*(lowerFourGridReal 128-lowerFourGridReal 0) := h
  nlinarith

/-- Page 51 display 5.17. Integrating b, c and d preserves a uniform
variation bound for the remaining a coordinate. -/
theorem four_exponent_inner_three_variation {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s : ℝ) :
    eVariationOn (fourExponentInnerThree ω ε s) (Set.Icc 0 1) ≤ ENNReal.ofReal 120100000 := by
  apply four_exponent_evariation_of_partition_bound
  intro z hm hmem n
  have hlen : lowerFourGridReal 128-lowerFourGridReal 0 ≤ 1 := by
    norm_num [lowerFourGridReal, lowerFourGridPoint]
  have hlr : lowerFourGridReal 0 ≤ lowerFourGridReal 128 := by
    norm_num [lowerFourGridReal, lowerFourGridPoint]
  have hwidth : z n-z 0 ≤ 1 := by
    have h0 := (hmem 0).1
    have hn := (hmem n).2
    linarith
  have shrink : ∀ T : ℝ, T ≤ 62100000*(lowerFourGridReal 128-lowerFourGridReal 0) → T ≤ 62100000 := by
    intro T hT
    nlinarith
  have hp : ∀ b c d : ℝ, (∑ i ∈ Finset.range n,
      |fourExponentKernel ω ε s (z (i+1)) b c d-fourExponentKernel ω ε s (z i) b c d|) ≤ 62100000 := by
    intro b c d
    have h := four_exponent_kernel_variation_a hω hz hε hε8 s b c d z hm (Nat.zero_le n)
    simpa only [Nat.Ico_zero_eq_range] using
      h.trans (by linarith : 2000000*(z n-z 0)+60100000 ≤ 62100000)
  have hp1 : ∀ b c : ℝ, (∑ i ∈ Finset.range n,
      |fourExponentInnerOne ω ε s (z (i+1)) b c-fourExponentInnerOne ω ε s (z i) b c|) ≤ 62100000 := by
    intro b c
    apply shrink
    exact four_exponent_integral_partition_variation
      (fun a d => fourExponentKernel ω ε s a b c d) z (Finset.range n) hlr
      (fun a => four_exponent_kernel_integrable_d hω hz hε hε8 s a b c _ _) (fun d _ => hp b c d)
  have hp2 : ∀ b : ℝ, (∑ i ∈ Finset.range n,
      |fourExponentInnerTwo ω ε s (z (i+1)) b-fourExponentInnerTwo ω ε s (z i) b|) ≤ 62100000 := by
    intro b
    apply shrink
    exact four_exponent_integral_partition_variation
      (fun a c => fourExponentInnerOne ω ε s a b c) z (Finset.range n) hlr
      (fun a => four_exponent_inner_one_integrable hω hz hε hε8 s a b _ _) (fun c _ => hp1 b c)
  have h := four_exponent_integral_partition_variation
    (fun a b => fourExponentInnerTwo ω ε s a b) z (Finset.range n) hlr
    (fun a => four_exponent_inner_two_integrable hω hz hε hε8 s a _ _) (fun b _ => hp2 b)
  have h' : (∑ i ∈ Finset.range n,
      |fourExponentInnerThree ω ε s (z (i+1))-fourExponentInnerThree ω ε s (z i)|) ≤
      62100000*(lowerFourGridReal 128-lowerFourGridReal 0) := h
  nlinarith

#print axioms four_exponent_inner_one_variation
#print axioms four_exponent_inner_two_variation
#print axioms four_exponent_inner_three_variation
end LeanLab.BHP1997.LowerShortC165

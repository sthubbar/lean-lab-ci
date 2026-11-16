/-
P0069, Section 5, page 51, display 5.17.
Support and ordering for the nested E4 kernels.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentInnerVariation517

namespace LeanLab.BHP1997.LowerShortC165
open Classical DecompC165d

/-- Page 51 display 5.17. Every E4 coordinate stays strictly inside the
integration box, including the epsilon margin at its lower endpoint. -/
theorem four_exponent_region_strict_box {ε a b c d : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hr : lowerFourRegion ε a b c d) :
    lowerFourGridReal 0 < a ∧ a < lowerFourGridReal 128 ∧
    lowerFourGridReal 0 < b ∧ b < lowerFourGridReal 128 ∧
    lowerFourGridReal 0 < c ∧ c < lowerFourGridReal 128 ∧
    lowerFourGridReal 0 < d ∧ d < lowerFourGridReal 128 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  norm_num [lowerFourGridReal, lowerFourGridPoint] at h1 h5 hε8 ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

/-- Page 51 display 5.17. The E4 kernel is zero if any coordinate lies
outside the interior of the integration box. -/
theorem four_exponent_kernel_box_zero {ω : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b c d : ℝ)
    (h : (a ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ a) ∨
      (b ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ b) ∨
      (c ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ c) ∨
      (d ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ d)) :
    fourExponentKernel ω ε s a b c d = 0 := by
  by_cases hr : lowerFourRegion ε a b c d
  · obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩ := four_exponent_region_strict_box hε hε8 hr
    rcases h with (h|h)|(h|h)|(h|h)|(h|h) <;> linarith
  · simp only [fourExponentKernel, if_neg hr]

/-- Page 51 display 5.17. The one-fold inner kernel is supported in the
interior of the grid box in its remaining last coordinate. -/
theorem four_exponent_inner_one_support {ω : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b c : ℝ)
    (hc : c ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ c) :
    fourExponentInnerOne ω ε s a b c = 0 := by
  unfold fourExponentInnerOne
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro d hd
  exact four_exponent_kernel_box_zero hε hε8 s a b c d (Or.inr (Or.inr (Or.inl hc)))

/-- Page 51 display 5.17. The two-fold inner kernel has the same support
in its remaining last coordinate. -/
theorem four_exponent_inner_two_support {ω : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b : ℝ)
    (hb : b ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ b) :
    fourExponentInnerTwo ω ε s a b = 0 := by
  unfold fourExponentInnerTwo fourExponentInnerOne
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro c hc
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro d hd
  exact four_exponent_kernel_box_zero hε hε8 s a b c d (Or.inr (Or.inl hb))

/-- Page 51 display 5.17. The three-fold inner kernel has the same support
in its remaining first coordinate. -/
theorem four_exponent_inner_three_support {ω : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a : ℝ)
    (ha : a ≤ lowerFourGridReal 0 ∨ lowerFourGridReal 128 ≤ a) :
    fourExponentInnerThree ω ε s a = 0 := by
  unfold fourExponentInnerThree fourExponentInnerTwo fourExponentInnerOne
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro b hb
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro c hc
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro d hd
  exact four_exponent_kernel_box_zero hε hε8 s a b c d (Or.inl ha)

/-- Page 51 display 5.17. The one-fold inner kernel vanishes above the
fixed second exponent by the E4 ordering. -/
theorem four_exponent_inner_one_order {ω : ℝ → ℝ} (ε s a b c : ℝ) (hcb : b < c) :
    fourExponentInnerOne ω ε s a b c = 0 := by
  unfold fourExponentInnerOne
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro d hd
  have hr : ¬ lowerFourRegion ε a b c d := by intro h; linarith [h.2.2.1]
  simp only [fourExponentKernel, if_neg hr]

/-- Page 51 display 5.17. The two-fold inner kernel vanishes above the
fixed first exponent by the E4 ordering. -/
theorem four_exponent_inner_two_order {ω : ℝ → ℝ} (ε s a b : ℝ) (hba : a < b) :
    fourExponentInnerTwo ω ε s a b = 0 := by
  unfold fourExponentInnerTwo fourExponentInnerOne
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro c hc
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro d hd
  have hr : ¬ lowerFourRegion ε a b c d := by intro h; linarith [h.2.2.2.1]
  simp only [fourExponentKernel, if_neg hr]

#print axioms four_exponent_region_strict_box
#print axioms four_exponent_kernel_box_zero
#print axioms four_exponent_inner_one_support
#print axioms four_exponent_inner_two_support
#print axioms four_exponent_inner_three_support
#print axioms four_exponent_inner_one_order
#print axioms four_exponent_inner_two_order
end LeanLab.BHP1997.LowerShortC165

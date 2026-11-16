/-
P0069, Section 5, page 51, display 5.17.
Finite sum bookkeeping for the first coordinate replacement, with the
last integer index treated on each fibre.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentScales517

namespace LeanLab.BHP1997.LowerShortC165
open Classical DecompC165d
open scoped BigOperators

/-- Page 51 display 5.17. The four integer sum is a weighted triple sum
of strict last coordinate fibres. -/
theorem four_exponent_mixed_zero_fibres (ω : ℝ → ℝ) (ε x s : ℝ) :
    let B := Finset.Icc 1 ⌊2*x ^ (11/20+ε)⌋₊
    let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log (scaleZ ε x))
    let e := expo ε x
    fourExponentMixed ω ε x s 0 =
      ∑ a ∈ B, w a * (∑ b ∈ B, w b * (∑ c ∈ B, w c *
        (if b < a ∧ c < b then
          ∑ d ∈ B, if d < c then fourExponentKernel ω ε s (e a) (e b) (e c) (e d) * w d else 0
        else 0))) := by
  let B := Finset.Icc 1 ⌊2*x ^ (11/20+ε)⌋₊
  let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log (scaleZ ε x))
  let e := expo ε x
  dsimp only [fourExponentMixed]
  rw [four_sum_filter_iter]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  change (∑ d ∈ B,
      if b < a ∧ c < b ∧ d < c ∧ lowerFourRegion ε (e a) (e b) (e c) (e d) then
        fourExponentKernel ω ε s (e a) (e b) (e c) (e d) * (w a*w b*w c*w d) else 0) =
    w a * (w b * (w c * (if b < a ∧ c < b then
      ∑ d ∈ B, if d < c then fourExponentKernel ω ε s (e a) (e b) (e c) (e d) * w d else 0
      else 0)))
  by_cases hba : b < a
  · by_cases hcb : c < b
    · simp only [hba, hcb, true_and, and_self, ite_true]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdc : d < c
      · by_cases hr : lowerFourRegion ε (e a) (e b) (e c) (e d)
        · simp only [hdc, hr, and_self, ite_true]
          ring
        · simp [hr, hdc, fourExponentKernel]
      · simp [hdc]
    · simp [hcb]
  · simp [hba]

/-- Page 51 display 5.17. The first mixed integral has the same weighted
triple sum form as the strict integer fibres. -/
theorem four_exponent_mixed_one_fibres (ω : ℝ → ℝ) (ε x s : ℝ) :
    let B := Finset.Icc 1 ⌊2*x ^ (11/20+ε)⌋₊
    let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log (scaleZ ε x))
    let e := expo ε x
    fourExponentMixed ω ε x s 1 =
      ∑ a ∈ B, w a * (∑ b ∈ B, w b * (∑ c ∈ B, w c *
        (if b < a ∧ c < b then
          ∫ d in lowerFourGridReal 0..lowerFourGridReal 128,
            fourExponentKernel ω ε s (e a) (e b) (e c) d
        else 0))) := by
  dsimp only [fourExponentMixed]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs <;> ring

#print axioms four_exponent_mixed_zero_fibres
#print axioms four_exponent_mixed_one_fibres
end LeanLab.BHP1997.LowerShortC165

/-
P0069, Section 5, page 51, display 5.17.
Finite sum forms for the three remaining coordinate replacements.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentFunction517
import LeanLab.BHP1997.FourExponentInnerSupport517
import LeanLab.BHP1997.FourExponentFirst517

namespace LeanLab.BHP1997.LowerShortC165
open Classical DecompC165d
open scoped BigOperators

/-- Page 51 display 5.17. The c coordinate difference is a weighted double
sum of the strict integer fibre errors of the first inner integral. -/
theorem four_exponent_mixed_c_difference (ω : ℝ → ℝ) (ε x s : ℝ) :
    let B := Finset.Icc 1 ⌊2*x ^ (11/20+ε)⌋₊
    let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log (scaleZ ε x))
    let e := expo ε x
    fourExponentMixed ω ε x s 1-fourExponentMixed ω ε x s 2 =
      ∑ a ∈ B, w a * (∑ b ∈ B, w b * (if b < a then
        (∑ c ∈ B, if c < b then fourExponentInnerOne ω ε s (e a) (e b) (e c)*w c else 0) -
          fourExponentInnerTwo ω ε s (e a) (e b) else 0)) := by
  let B := Finset.Icc 1 ⌊2*x ^ (11/20+ε)⌋₊
  let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log (scaleZ ε x))
  let e := expo ε x
  dsimp only [fourExponentMixed]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  change (∑ c ∈ B, if b < a ∧ c < b then
      fourExponentInnerOne ω ε s (e a) (e b) (e c)*(w a*w b*w c) else 0) -
      (if b < a then fourExponentInnerTwo ω ε s (e a) (e b)*(w a*w b) else 0) =
    w a * (w b * (if b < a then
      (∑ c ∈ B, if c < b then fourExponentInnerOne ω ε s (e a) (e b) (e c)*w c else 0) -
        fourExponentInnerTwo ω ε s (e a) (e b) else 0))
  by_cases hba : b < a
  · simp only [hba, true_and, ite_true]
    have hsum : (∑ c ∈ B, if c < b then
        fourExponentInnerOne ω ε s (e a) (e b) (e c)*(w a*w b*w c) else 0) =
      w a * (w b * (∑ c ∈ B, if c < b then
        fourExponentInnerOne ω ε s (e a) (e b) (e c)*w c else 0)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hcb : c < b <;> simp only [hcb, ite_true, ite_false] <;> ring
    rw [hsum]
    ring
  · simp [hba]

/-- Page 51 display 5.17. The b coordinate difference is a weighted single
sum of strict integer fibre errors of the second inner integral. -/
theorem four_exponent_mixed_b_difference (ω : ℝ → ℝ) (ε x s : ℝ) :
    let B := Finset.Icc 1 ⌊2*x ^ (11/20+ε)⌋₊
    let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log (scaleZ ε x))
    let e := expo ε x
    fourExponentMixed ω ε x s 2-fourExponentMixed ω ε x s 3 =
      ∑ a ∈ B, w a * ((∑ b ∈ B, if b < a then
        fourExponentInnerTwo ω ε s (e a) (e b)*w b else 0) -
          fourExponentInnerThree ω ε s (e a)) := by
  let B := Finset.Icc 1 ⌊2*x ^ (11/20+ε)⌋₊
  let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log (scaleZ ε x))
  let e := expo ε x
  dsimp only [fourExponentMixed]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  change (∑ b ∈ B, if b < a then fourExponentInnerTwo ω ε s (e a) (e b)*(w a*w b) else 0) -
      fourExponentInnerThree ω ε s (e a)*w a =
    w a * ((∑ b ∈ B, if b < a then fourExponentInnerTwo ω ε s (e a) (e b)*w b else 0) -
      fourExponentInnerThree ω ε s (e a))
  have hsum : (∑ b ∈ B, if b < a then fourExponentInnerTwo ω ε s (e a) (e b)*(w a*w b) else 0) =
      w a * (∑ b ∈ B, if b < a then fourExponentInnerTwo ω ε s (e a) (e b)*w b else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hba : b < a <;> simp only [hba, ite_true, ite_false] <;> ring
  rw [hsum]
  ring

/-- Page 51 display 5.17. The a coordinate difference is the scalar
integer quadrature of the three-fold inner integral. -/
theorem four_exponent_mixed_a_difference (ω : ℝ → ℝ) (ε x s : ℝ) :
    let B := Finset.Icc 1 ⌊2*x ^ (11/20+ε)⌋₊
    let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log (scaleZ ε x))
    let e := expo ε x
    fourExponentMixed ω ε x s 3-fourExponentMixed ω ε x s 4 =
      (∑ a ∈ B, fourExponentInnerThree ω ε s (e a)*w a) -
        ∫ a in lowerFourGridReal 0..lowerFourGridReal 128, fourExponentInnerThree ω ε s a := by
  rfl

/-- Page 51 display 5.17. A nonnegative outer weight sum of mass at most
two multiplies a uniform fibre error by at most two. -/
theorem four_exponent_weight_contraction (B : Finset ℕ) (w G : ℕ → ℝ) {E : ℝ}
    (hE : 0 ≤ E) (hw : ∀ n ∈ B, 0 ≤ w n) (hW : ∑ n ∈ B, w n ≤ 2)
    (hG : ∀ n ∈ B, |G n| ≤ E) : |∑ n ∈ B, w n*G n| ≤ 2*E := by
  calc _ ≤ ∑ n ∈ B, |w n*G n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ B, w n*E := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (hw n hn)]
      exact mul_le_mul_of_nonneg_left (hG n hn) (hw n hn)
    _ = (∑ n ∈ B, w n)*E := (Finset.sum_mul _ _ _).symm
    _ ≤ 2*E := mul_le_mul_of_nonneg_right hW hE

#print axioms four_exponent_mixed_c_difference
#print axioms four_exponent_mixed_b_difference
#print axioms four_exponent_mixed_a_difference
#print axioms four_exponent_weight_contraction
end LeanLab.BHP1997.LowerShortC165

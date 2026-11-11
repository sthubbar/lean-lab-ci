/-
AI wrote this Lean code. Codex task423.
Binary Goldbach is open.
Source: Heath Brown 1982 page 1367, the hypotheses before the grouping argument.
This verifies the Tolev scales only. It does not prove the retained identity.
-/
import Mathlib

open Real
namespace LeanLab.Tolev2009.RetainedBudget423

/-- The printed Tolev scales satisfy all numerical hypotheses of the written grouping proof.
Heath Brown page 1367 and Tolev 1999 page 82. -/
theorem grouping_scales (t : ℝ) (ht : 3000 ≤ t) :
    let x := (2 : ℝ) ^ t
    let u := x ^ ((1 : ℝ) / 1000)
    let v := 2 ^ (30 : ℕ) * x ^ ((1 : ℝ) / 3)
    let z := x ^ ((249 : ℝ) / 500)
    2 ≤ u ∧ u ≤ v ∧ v ≤ z ∧ z ≤ x ∧ u ^ 2 ≤ z ∧
      128 * u * z ^ 2 ≤ x ∧ 2 ^ (18 : ℕ) * x ≤ v ^ 3 := by
  have hm {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  dsimp only
  rw [show (128 : ℝ) = (2 : ℝ) ^ (7 : ℝ) by norm_num [Real.rpow_natCast]]
  simp only [← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine ⟨?_, hm (by linarith), hm (by linarith), hm (by linarith),
    hm (by linarith), hm (by linarith), hm (by linarith)⟩
  simpa only [Real.rpow_one] using hm (show 1 ≤ t * ((1 : ℝ) / 1000) by linarith)

/-- The algebraic k equal to three case of Heath Brown page 1367 display 6.
The analytic substitutions and coefficient extraction are separate steps. -/
theorem identity_k3 (z d m : ℂ) (hz : z ≠ 0) :
    d / z = 3 * d * m - 3 * z * d * m ^ 2 + z ^ 2 * d * m ^ 3 +
      (1 - z * m) ^ 3 * d / z := by
  field_simp
  ring

/-- A Dirichlet convolution vanishes below the product of its support thresholds.
Heath Brown page 1367 display 7, the finite coefficient support mechanism. -/
theorem convolution_vanish (f g : ArithmeticFunction ℂ) (X Y n : ℕ)
    (hf : ∀ a, a ≤ X → f a = 0) (hg : ∀ b, b ≤ Y → g b = 0)
    (hn : n ≤ X * Y) : (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  have hp : ab.1 * ab.2 = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
  by_cases ha : ab.1 ≤ X
  · rw [hf _ ha, zero_mul]
  · have hb : ab.2 ≤ Y := by
      by_contra h
      have hmul := Nat.mul_le_mul (show X + 1 ≤ ab.1 by omega)
        (show Y + 1 ≤ ab.2 by omega)
      nlinarith
    rw [hg _ hb, mul_zero]

/-- The cubic error convolution has no coefficient below the cubed threshold.
Heath Brown page 1367 displays 6 and 7. -/
theorem convolution_cube_vanish (f : ArithmeticFunction ℂ) (X n : ℕ)
    (hf : ∀ a, a ≤ X → f a = 0) (hn : n ≤ X ^ 3) : (f ^ 3) n = 0 := by
  have hsquare : ∀ a, a ≤ X * X → (f * f) a = 0 :=
    fun a ha => convolution_vanish f f X X a hf hf ha
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  apply convolution_vanish (f * f) f (X * X) X n hsquare hf
  nlinarith [hn]

end LeanLab.Tolev2009.RetainedBudget423

/-
The arithmetic sparsity statement quoted from Pintz on page 23 displays 6.6 and 6.7.
This file states the cited input. It asserts no theorem or axiom.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

/-- CITED. Page 23 displays 6.6 and 6.7, the Main Lemma of Pintz quoted there.
For sufficiently small positive eta, the generalized singular series is at most eta
unless both conductors divide a bounded positive integer multiple of N and the product
character has conductor less than eta to power negative three.
The product character is formed at the least common multiple level by Mathlib. -/
def GenSingSparsity84 : Prop :=
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ → ∃ C : ℕ, 1 ≤ C ∧
    ∀ (r₁ r₂ : ℕ) [NeZero r₁] [NeZero r₂]
      (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂),
      χ₁.IsPrimitive → χ₂.IsPrimitive → ∀ N : ℕ, 1 ≤ N →
      ¬ (r₁ ∣ C * N ∧ r₂ ∣ C * N ∧
        ((DirichletCharacter.mul χ₁ χ₂).conductor : ℝ) < 1 / η ^ 3) →
      ‖genSing χ₁ χ₂ N‖ ≤ η

end LeanLab.BhowmikGrimmelt2026

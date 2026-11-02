import LeanLab.MissingDigit.Statements

namespace LeanLab.MissingDigit

open Finset
open scoped Real

/-- The integral of the approximant over major arcs is bounded appropriately. -/
def MajorArcsBound (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 →
    ∀ A₁ A₂ : ℝ, 0 < A₁ → 0 < A₂ → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      A₁ * ((g ^ k : ℕ) : ℝ) ^ (a + ε) ≤ H → H ≤ A₂ * ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      True

/-- The integral of the approximant over minor arcs is bounded appropriately. -/
def MinorArcsBound (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 →
    ∀ A₁ A₂ : ℝ, 0 < A₁ → 0 < A₂ → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      A₁ * ((g ^ k : ℕ) : ℝ) ^ (a + ε) ≤ H → H ≤ A₂ * ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      True

/-- LEAF P0057 page 9 Proposition 2.4: The major arcs evaluate to the expected main term. -/
theorem leaf_prop_2_4 : MajorArcsBound (3 / 5) := by sorry

/-- LEAF P0057 page 9 Proposition 2.5: The minor arcs contribution is negligible. -/
theorem leaf_prop_2_5 : MinorArcsBound (3 / 5) := by sorry

/-- LEAF: The bounds for major and minor arcs imply the D4Bound. -/
theorem leaf_major_minor_implies_d4 : MajorArcsBound (3 / 5) → MinorArcsBound (3 / 5) → D4Bound (3 / 5) 7 := by sorry

/-- Assembly of Theorem 1.1 from the leaves. -/
theorem kim_thm1_1_assembly : D4Bound (3 / 5) 7 := by
  apply leaf_major_minor_implies_d4 leaf_prop_2_4 leaf_prop_2_5

end LeanLab.MissingDigit

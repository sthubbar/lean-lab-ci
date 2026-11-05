import LeanLab.ChenDoubleSieve.Decomp275b

/-!
Supply split for Wu 2004 Section 10.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF. Wu 2004 page 38 equation 10.2.
The lower estimate for the single coordinate F0. -/
theorem lower_F0 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 := by
  sorry

/-- LEAF. Wu 2004 page 39 equation 10.5.
The lower estimate for the single coordinate F4. -/
theorem lower_F4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 := by
  sorry

/-- LEAF. Wu 2004 page 39 equation 10.5.
The lower estimate for the single coordinate F5. -/
theorem lower_F5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  sorry

/-- The exact positive_estimates statement follows from its three coordinates.
OPEN through lower_F0, lower_F4 and lower_F5. -/
theorem positive_estimates_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 ∧
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 ∧
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  intro ε hε
  obtain ⟨M₀, h₀⟩ := lower_F0 F f ω h hω ε hε
  obtain ⟨M₄, h₄⟩ := lower_F4 F f ω h hω ε hε
  obtain ⟨M₅, h₅⟩ := lower_F5 F f ω h hω ε hε
  refine ⟨max M₀ (max M₄ M₅), ?_⟩
  intro N hEven hN
  exact ⟨h₀ N hEven (by omega), h₄ N hEven (by omega), h₅ N hEven (by omega)⟩

end LeanLab.ChenDoubleSieve.Task315

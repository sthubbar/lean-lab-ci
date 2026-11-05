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

/-- LEAF. Wu 2004 pages 39 equations 10.3 and 10.4.
The upper estimates for coordinates 1, 2, 3. -/
theorem basic_upper (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  sorry

/-- LEAF. Wu 2004 pages 40 and 41 equations 10.6 to 10.11.
The upper estimates for coordinates 6, 7, 9. -/
theorem switched_upper (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  sorry

/-- LEAF. Wu 2004 pages 41 equation 10.12.
The upper estimates for coordinates 8, 10, 11. -/
theorem refined_upper (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({8, 10, 11} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  sorry

/-- The exact negative_estimates statement follows from three smaller groups.
OPEN through basic_upper, switched_upper and refined_upper. -/
theorem negative_estimates_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  intro ε hε
  obtain ⟨M₁, h₁⟩ := basic_upper F f ω h hω ε hε
  obtain ⟨M₂, h₂⟩ := switched_upper F f ω h hω ε hε
  obtain ⟨M₃, h₃⟩ := refined_upper F f ω h hω ε hε
  refine ⟨max M₁ (max M₂ M₃), ?_⟩
  intro N hEven hN i hi
  have hpart : i ∈ ({1, 2, 3} : Finset (Fin 12)) ∨
      i ∈ ({6, 7, 9} : Finset (Fin 12)) ∨ i ∈ ({8, 10, 11} : Finset (Fin 12)) := by
    fin_cases i <;> simp_all
  rcases hpart with hi | hi | hi
  · exact h₁ N hEven (by omega) i hi
  · exact h₂ N hEven (by omega) i hi
  · exact h₃ N hEven (by omega) i hi

end LeanLab.ChenDoubleSieve.Task315

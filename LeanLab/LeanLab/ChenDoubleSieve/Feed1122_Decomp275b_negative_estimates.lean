import LeanLab.ChenDoubleSieve.Decomp275b

/-!
SPLIT of `Task275.negative_estimates` into its nine printed upper bounds, one per index.
Source: Wu 2004, https://arxiv.org/pdf/0705.1652, pages 39 to 41, equations 10.3, 10.4, 10.10 to 10.12.
This file imports Decomp275b because the parent's statement uses the definitions
`sieveTerms`, `integralTerms` and `Θ` that live there; the original is not edited.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Neg
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 39 equation 10.3, upper bound for Upsilon 1, the sum over primes p between N to the kappa one and N to the kappa two of S at level p, giving F1. Index 1 of sieveTerms. Class HARD. -/
theorem leaf_term1 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 1 ≤ (integralTerms F f ω 1 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 39 equation 10.4 with sigma one, upper bound for the sum over p between N to the kappa one and N to the sigma one, giving F2. Index 2 of sieveTerms. Class HARD. -/
theorem leaf_term2 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 2 ≤ (integralTerms F f ω 2 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 39 equation 10.4 with sigma two, upper bound for the sum over p between N to the kappa one and N to the sigma two, giving F3. Index 3 of sieveTerms. Class HARD. -/
theorem leaf_term3 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 3 ≤ (integralTerms F f ω 3 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 40 equation 10.10, upper bound for Upsilon 7 obtained by inserting 10.7 to 10.9 into 10.6, giving F7. Index 6 of sieveTerms. Class HARD. -/
theorem leaf_term6 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 6 ≤ (integralTerms F f ω 6 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.11 with i equal 8, upper bound for Upsilon 8, giving F8. Index 7 of sieveTerms. Class HARD. -/
theorem leaf_term7 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 7 ≤ (integralTerms F f ω 7 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12 with i equal 9, upper bound for Upsilon 9 via Lemma 2.6 and 3 sigma one plus kappa one above 1, giving F9. Index 8 of sieveTerms. Class HARD. -/
theorem leaf_term8 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 8 ≤ (integralTerms F f ω 8 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.11 with i equal 10, upper bound for Upsilon 10 using 2 sigma one plus sigma two plus kappa two above 1, giving F10. Index 9 of sieveTerms. Class HARD. -/
theorem leaf_term9 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 9 ≤ (integralTerms F f ω 9 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12 with i equal 13, upper bound for Upsilon 13 via Lemma 2.6 and Lemma 2.10, giving F13. Index 10 of sieveTerms. Class HARD. -/
theorem leaf_term10 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 10 ≤ (integralTerms F f ω 10 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12 with i equal 14, upper bound for Upsilon 14 via Lemma 2.6 and Lemma 2.10, giving F14. Index 11 of sieveTerms. Class HARD. -/
theorem leaf_term11 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 11 ≤ (integralTerms F f ω 11 + ε) * Θ N := by
  sorry

/-- The parent `negative_estimates`, exactly as stated in Decomp275b, from the nine leaves. -/
theorem negative_estimates_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  intro ε hε
  obtain ⟨A1, h1⟩ := leaf_term1 F f ω h hω ε hε
  obtain ⟨A2, h2⟩ := leaf_term2 F f ω h hω ε hε
  obtain ⟨A3, h3⟩ := leaf_term3 F f ω h hω ε hε
  obtain ⟨A6, h6⟩ := leaf_term6 F f ω h hω ε hε
  obtain ⟨A7, h7⟩ := leaf_term7 F f ω h hω ε hε
  obtain ⟨A8, h8⟩ := leaf_term8 F f ω h hω ε hε
  obtain ⟨A9, h9⟩ := leaf_term9 F f ω h hω ε hε
  obtain ⟨A10, h10⟩ := leaf_term10 F f ω h hω ε hε
  obtain ⟨A11, h11⟩ := leaf_term11 F f ω h hω ε hε
  refine ⟨A1 + A2 + A3 + A6 + A7 + A8 + A9 + A10 + A11, ?_⟩
  intro N hN hle i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 N hN (by omega)
  · exact h2 N hN (by omega)
  · exact h3 N hN (by omega)
  · exact h6 N hN (by omega)
  · exact h7 N hN (by omega)
  · exact h8 N hN (by omega)
  · exact h9 N hN (by omega)
  · exact h10 N hN (by omega)
  · exact h11 N hN (by omega)

end LeanLab.ChenDoubleSieve.Task275.Feed1122Neg

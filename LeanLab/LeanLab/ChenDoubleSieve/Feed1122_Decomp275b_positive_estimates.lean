import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Feed1122_Decomp315b_lower_F5

/-!
SPLIT of `Task275.positive_estimates` into its three printed lower bounds.
Source: Wu 2004, https://arxiv.org/pdf/0705.1652, pages 38 and 39, equations 10.2 and 10.5.
This file imports Decomp275b because the parent's statement uses the definitions
`sieveTerms`, `integralTerms` and `Θ` that live there; the original is not edited.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Pos
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 38 equation 10.2, lower linear sieve bound for S of the prime
sequence at level N to the kappa one, giving the main term F0. Class HARD. -/
theorem leaf_term0 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 := by
  exact LeanLab.ChenDoubleSieve.Task315.Feed1122F0.lower_F0_of_leaves F f ω h hω

/-- LEAF: Wu 2004 page 39 equation 10.5, first display, lower bound for the bilinear
sum over kappa one at most p less than q less than N to the kappa two, giving F4. Class HARD. -/
theorem leaf_term4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 := by
  exact LeanLab.ChenDoubleSieve.Task315.Feed1122F0.lower_F4_of_leaves F f ω h hω

/-- LEAF: Wu 2004 page 39 equation 10.5, second display, lower bound for the bilinear
sum with q between N to the kappa two and N to the half minus two kappa one over p,
giving F5. Class HARD. -/
theorem leaf_term5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  exact LeanLab.ChenDoubleSieve.Task315.Feed1122F0.lower_F5_of_leaves F f ω h hω

/-- The parent `positive_estimates`, exactly as stated in Decomp275b, from the three leaves. -/
theorem positive_estimates_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 ∧
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 ∧
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  intro ε hε
  obtain ⟨A, hA⟩ := leaf_term0 F f ω h hω ε hε
  obtain ⟨B, hB⟩ := leaf_term4 F f ω h hω ε hε
  obtain ⟨C, hC⟩ := leaf_term5 F f ω h hω ε hε
  refine ⟨max A (max B C), fun N hN hle => ⟨hA N hN ?_, hB N hN ?_, hC N hN ?_⟩⟩ <;> omega

end LeanLab.ChenDoubleSieve.Task275.Feed1122Pos

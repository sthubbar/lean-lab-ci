import LeanLab.ChenDoubleSieve.Feed1122_Decomp315c_basic_upper

/-!
Feed split of `refined_upper` in `Decomp315c`, Wu 2004 Section 10, page 41, equation 10.12.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
The group upper estimate is split into its three coordinates, each a separate display.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315.Feed1122Up
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 41, equations 10.9 to 10.11, upper bound for F9 by the switching principle with the refined weight 36 over 5 on t below one tenth. Class HARD. -/
theorem upper_8 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 8 ≤ (integralTerms F f ω 8 + ε) * Θ N := by
  intro ε hε
  obtain ⟨N0, hN0⟩ := Task349.refined_upper_supplied F f ω h hω ε hε
  exact ⟨N0, fun N hN hle => hN0 N hN hle 8 (by simp)⟩

/-- LEAF: Wu 2004 page 41, equation 10.12, upper bound for F13, the fourfold Buchstab integral with t four up to kappa two. Class HARD. -/
theorem upper_10 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 10 ≤ (integralTerms F f ω 10 + ε) * Θ N := by
  intro ε hε
  obtain ⟨N0, hN0⟩ := Task349.refined_upper_supplied F f ω h hω ε hε
  exact ⟨N0, fun N hN hle => hN0 N hN hle 10 (by simp)⟩

/-- LEAF: Wu 2004 page 41, equation 10.12, upper bound for F14, the fourfold Buchstab integral with t four up to one half minus two kappa one minus t three. Class HARD. -/
theorem upper_11 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 11 ≤ (integralTerms F f ω 11 + ε) * Θ N := by
  intro ε hε
  obtain ⟨N0, hN0⟩ := Task349.refined_upper_supplied F f ω h hω ε hε
  exact ⟨N0, fun N hN hle => hN0 N hN hle 11 (by simp)⟩

theorem refined_upper_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({8, 10, 11} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N :=
  group_of_three F f ω 8 10 11 (upper_8 F f ω h hω) (upper_10 F f ω h hω)
    (upper_11 F f ω h hω)

end LeanLab.ChenDoubleSieve.Task315.Feed1122Up

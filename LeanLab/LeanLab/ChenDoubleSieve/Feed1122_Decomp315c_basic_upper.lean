import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Decomp349c

/-!
Feed split of `basic_upper` in `Decomp315c`, Wu 2004 Section 10, pages 39, equations 10.3 and 10.4.
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

/-- Three coordinate upper estimates give the group estimate. -/
theorem group_of_three (F f ω : ℝ → ℝ) (a b c : Fin 12)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N a ≤ (integralTerms F f ω a + ε) * Θ N)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N b ≤ (integralTerms F f ω b + ε) * Θ N)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N c ≤ (integralTerms F f ω c + ε) * Θ N) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({a, b, c} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  intro ε hε
  obtain ⟨M₁, h₁⟩ := ha ε hε
  obtain ⟨M₂, h₂⟩ := hb ε hε
  obtain ⟨M₃, h₃⟩ := hc ε hε
  refine ⟨max M₁ (max M₂ M₃), fun N hN hle i hi => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact h₁ N hN (by omega)
  · exact h₂ N hN (by omega)
  · exact h₃ N hN (by omega)

/-- LEAF: Wu 2004 page 39, equation 10.3, upper bound for F1, the sum over N to the kappa one at most p below N to the kappa two of S of A sub p sifted up to p, by the linear sieve upper bound with Bombieri Vinogradov and partial summation. Class HARD. -/
theorem upper_1 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 1 ≤ (integralTerms F f ω 1 + ε) * Θ N := by
  intro ε hε
  obtain ⟨N0, hN0⟩ := Task349.basic_upper_supplied F f ω h hω ε hε
  exact ⟨N0, fun N hN hle => hN0 N hN hle 1 (by simp)⟩

/-- LEAF: Wu 2004 page 39, equation 10.4, upper bound for F2, the sum over p from N to the kappa one to N to the sigma one of S of A sub p sifted up to N to the kappa one, linear sieve upper bound at level N to the one half over p. Class HARD. -/
theorem upper_2 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 2 ≤ (integralTerms F f ω 2 + ε) * Θ N := by
  intro ε hε
  obtain ⟨N0, hN0⟩ := Task349.basic_upper_supplied F f ω h hω ε hε
  exact ⟨N0, fun N hN hle => hN0 N hN hle 2 (by simp)⟩

/-- LEAF: Wu 2004 page 39, equation 10.4, upper bound for F3, the same with sigma two in place of sigma one. Class HARD. -/
theorem upper_3 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 3 ≤ (integralTerms F f ω 3 + ε) * Θ N := by
  intro ε hε
  obtain ⟨N0, hN0⟩ := Task349.basic_upper_supplied F f ω h hω ε hε
  exact ⟨N0, fun N hN hle => hN0 N hN hle 3 (by simp)⟩

theorem basic_upper_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N :=
  group_of_three F f ω 1 2 3 (upper_1 F f ω h hω) (upper_2 F f ω h hω)
    (upper_3 F f ω h hω)

end LeanLab.ChenDoubleSieve.Task315.Feed1122Up

import LeanLab.ChenDoubleSieve.Feed1122_Decomp315c_basic_upper
import LeanLab.ChenDoubleSieve.Decomp349b

/-!
Feed split of `switched_upper` in `Decomp315c`, Wu 2004 Section 10, pages 40 and 41, equations 10.6 to 10.11.
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

/-- LEAF: Wu 2004 pages 40 and 41, equations 10.6 to 10.8, upper bound for F7 by the switching principle, the integral 8 times the integral from 2 to 1 over sigma one minus 1 of log of t minus 1 over t. Class HARD. -/
theorem upper_6 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 6 ≤ (integralTerms F f ω 6 + ε) * Θ N := by
  intro ε hε
  obtain ⟨N0, hN0⟩ :=
    LeanLab.ChenDoubleSieve.Task349.switched_upper_supplied F f ω h hω ε hε
  refine ⟨N0, ?_⟩
  intro N hEven hN
  exact hN0 N hEven hN 6 (by decide)

/-- LEAF: Wu 2004 pages 40 and 41, equations 10.6 to 10.8, upper bound for F8 by the switching principle with sigma two. Class HARD. -/
theorem upper_7 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 7 ≤ (integralTerms F f ω 7 + ε) * Θ N := by
  sorry

/-- LEAF: Wu 2004 page 41, equations 10.9 to 10.11, upper bound for F10 by the switching principle, the integral from kappa two to sigma two. Class HARD. -/
theorem upper_9 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 9 ≤ (integralTerms F f ω 9 + ε) * Θ N := by
  sorry

theorem switched_upper_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N :=
  group_of_three F f ω 6 7 9 (upper_6 F f ω h hω) (upper_7 F f ω h hω)
    (upper_9 F f ω h hω)

end LeanLab.ChenDoubleSieve.Task315.Feed1122Up

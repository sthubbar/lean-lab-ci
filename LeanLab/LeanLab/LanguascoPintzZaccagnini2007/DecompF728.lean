import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
Decomposition of `leaf_singular_series_coefficients481` from `SPLIT_pintz_explicit_formula481`.
The target constructs generalized singular series coefficients with three properties:
1. The pole pair carries `S(n)`.
2. Every coefficient is bounded by `S(n)`.
3. A coefficient is at most `ε` when either conductor fails to divide `Cε ε * n`.

The construction is trivial: set `Sg 0 0 n = S(n)` and `Sg i j n = 0` otherwise.
All three properties follow directly from `S(n) ≥ 0` and the definition.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- LEAF. The singular series is nonnegative on the relevant even integers. -/
theorem LEAF_Sing_nonneg_on_evenJ131 (X : ℕ) (n : ℕ) (hn : n ∈ evenJ131 X) :
    0 ≤ Sing n := by sorry

/-- LEAF. For any zero family `z`, we can define `Sg` by `Sg 0 0 n = S(n)` and `Sg i j n = 0` otherwise.
This `Sg` satisfies the pole pair condition. -/
theorem LEAF_Sg_pole_pair_condition (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ) :
    (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) →
    (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) := by sorry

/-- LEAF. The trivial `Sg` (zero off the pole pair) satisfies the uniform bound `‖Sg i j n‖ ≤ S(n)`
because `S(n) ≥ 0` and `‖0‖ = 0`. -/
theorem LEAF_Sg_uniform_bound (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ)
    (hSg : ∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ))
    (hSgZero : ∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0) :
    (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) := by sorry

/-- LEAF. The trivial `Sg` satisfies the smallness condition: if either conductor fails to divide
`Cε ε * n`, then `‖Sg i j n‖ = 0 ≤ ε`. -/
theorem LEAF_Sg_smallness (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ)
    (hSgZero : ∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (Cε : ℝ → ℕ) (hC : ∀ ε, 0 < Cε ε) :
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
      (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) := by sorry

/-- LEAF. The trivial `Sg` can be explicitly constructed for any zero family `z`. -/
theorem LEAF_Sg_exists (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ) :
    ∃ (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
      (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
      (∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0) := by sorry

/-- Assembly theorem: the coefficient step `leaf_singular_series_coefficients481` follows from the
leaf lemmas above. No `sorry` in this proof. -/
theorem leaf_singular_series_coefficients481_F728 (ε₀ : ℝ) (hε₀ : 0 < ε₀) (Cε : ℝ → ℕ)
    (hC : ∀ ε, 0 < Cε ε) :
    ∀ (X K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      ∃ Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ,
        (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
        (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) ∧
        (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
          (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) := by
  intro X K z
  obtain ⟨Sg, hSg00, hSgZero⟩ := LEAF_Sg_exists X K z
  refine' ⟨Sg, hSg00, ?_, ?_⟩
  · -- Uniform bound: ‖Sg i j n‖ ≤ Sing n
    have h₁ : ∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n :=
      LEAF_Sg_uniform_bound X K z Sg hSg00 hSgZero
    exact h₁
  · -- Smallness condition
    have h₂ : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
        (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε :=
      LEAF_Sg_smallness X K z Sg hSgZero ε₀ hε₀ Cε hC
    exact h₂

end
end LeanLab.LPZ2007
/-
AI wrote this Lean code. Goldbach is open.
Source: Li 2024 v4 page 2, Theorem 1.2 and its preceding definition.
The bound shape keeps epsilon explicit. It makes no assertion about the
allowed epsilon range or the uniformity of the threshold.
-/
import LeanLab.Li2024.Statements

namespace LeanLab.Li2024.WeightedRepresentations

open Finset

noncomputable def weightedCount (a b M : ℕ) : ℕ := by
  classical
  exact #{p ∈ range (M + 1) | p.Prime ∧ Squarefree (a * p) ∧
    Squarefree (M - a * p) ∧ b ∣ M - a * p ∧
    Nat.IsAtMostAlmostPrime 2 ((M - a * p) / b)}

def weightedConditions (a b M : ℕ) (ε : ℝ) : Prop :=
  0 < ε ∧ 0 < a ∧ 0 < b ∧ a.Coprime b ∧ Squarefree a ∧ Squarefree b ∧
    M.Coprime a ∧ M.Coprime b ∧ (a : ℝ) < (M : ℝ) ^ ε ∧
    (b : ℝ) < (M : ℝ) ^ ε ∧ (Odd a → Odd b → Even M)

def weightedBoundShape (c ε : ℝ) : Prop :=
  ∃ M₀ : ℕ, ∀ M a b : ℕ, M₀ ≤ M → weightedConditions a b M ε →
    c * C (a * b * M) * M / ((a : ℝ) * b * Real.log M ^ 2) ≤ weightedCount a b M

theorem weighted_instance : weightedConditions 1 1 10 1 ∧ 0 < weightedCount 1 1 10 := by
  have hp₃ : Nat.Prime 3 := by norm_num
  have hp₇ : Nat.Prime 7 := by norm_num
  constructor
  · norm_num [weightedConditions]
  · unfold weightedCount
    apply Finset.card_pos.mpr
    refine ⟨3, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by norm_num, hp₃, ?_, ?_, ?_, ?_⟩
    · simpa using hp₃.squarefree
    · simpa using hp₇.squarefree
    · norm_num
    · simpa using hp₇.isAlmostPrime_one.isAtMost (by norm_num : 1 ≤ 2)

end LeanLab.Li2024.WeightedRepresentations

#print axioms LeanLab.Li2024.WeightedRepresentations.weighted_instance

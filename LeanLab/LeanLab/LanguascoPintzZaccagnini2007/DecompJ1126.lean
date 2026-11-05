/-
Decomposition of cor42_published131 into smaller leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218

namespace LeanLab.LPZ2007

open Finset

/-- LEAF. Helper definition to extract the first bound condition. -/
def BoundCondition1 (η : ℝ) (Cstar : ℕ) (X : ℕ) (P : ℝ) (E : Finset ℕ) (W : ℕ → Finset ℕ) : Prop :=
  ∀ n ∈ W X, Nonexceptional131 Cstar E n →
    |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n

/-- LEAF. Helper definition to extract the second bound condition. -/
def BoundCondition2 (A : ℝ) (X : ℕ) (P : ℝ) (W : ℕ → Finset ℕ) : Prop :=
  ∀ n ∈ W X, |binaryMajor131 X n P| ≤ A * n * Sing n

/-- LEAF. Published Corollary 4.2 with Lemma 4.1, part 1. -/
theorem cor42_published131_part1 (η : ℝ) (hη : 0 < η) :
    ∃ (K₁ Cstar : ℕ) (c : ℝ), 0 < Cstar ∧ 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
        BoundCondition1 η Cstar X P E evenJ131 := by
  sorry

/-- LEAF. Published Corollary 4.2 with Lemma 4.1, part 2. -/
theorem cor42_published131_part2 :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ), AdmissibleP131 X P ∧
        BoundCondition2 A X P evenJ131 := by
  sorry

/-- LEAF. Combining the two parts yields the full condition. -/
theorem cor42_published131_combine (η : ℝ) (hη : 0 < η) :
    (∃ (K₁ Cstar : ℕ) (c : ℝ), 0 < Cstar ∧ 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
        BoundCondition1 η Cstar X P E evenJ131) →
    (∃ A : ℝ, 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ), AdmissibleP131 X P ∧
        BoundCondition2 A X P evenJ131) →
    ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
        (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
        (∀ n ∈ evenJ131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) := by
  sorry

/-- Assembly of the cor42_published131 target from its leaves. -/
theorem cor42_published131_assembly : Cor42OnWindow131 evenJ131 := by
  intro η hη
  exact cor42_published131_combine η hη (cor42_published131_part1 η hη) cor42_published131_part2

end LeanLab.LPZ2007

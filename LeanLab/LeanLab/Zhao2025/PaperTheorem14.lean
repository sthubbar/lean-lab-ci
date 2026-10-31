import Mathlib

/-!
The paper's prime counting assertion is stated as a Prop, not assumed as an axiom.
Source: Zhao 2025, displays 1.15 and 1.16, page 3.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The exact finite prime count in the progression a modulo q up to X. -/
noncomputable def primeCountAP (X : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.range (⌊X⌋₊ + 1)).filter fun p => Nat.Prime p ∧ p % q = a % q).card

/-- STATED and cited. The threshold is taken after theta is fixed. -/
def PaperTheorem14 : Prop :=
  ∀ theta : ℝ, 5 ≤ theta → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
      ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
        0 < (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ∧
        (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
          (2 + epsilon) * (q : ℝ) ^ theta /
            ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta))

/-- The arithmetic hypotheses of Theorem 1.4 have concrete instances. -/
theorem theorem14_hypotheses :
    5 ≤ (5 : ℝ) ∧ 0 < (1 : ℝ) ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ (2 : ℕ) ∧ Nat.Coprime 1 2 := by
  norm_num

#print axioms theorem14_hypotheses

end LeanLab.Zhao2025.Task56

import LeanLab.Xi2012.NatEncoding

/-!
Xi 2012, arXiv 1206.2148v1, page 3 final paragraph.
The claimed two-family extension is a proposition, not an asserted theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

open Finset Real

/-- A sum with one summand in each family. -/
def IsMixedSumIn (X Y : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p ∈ X, ∃ q ∈ Y, p + q = n

instance (X Y : Finset ℕ) (n : ℕ) : Decidable (IsMixedSumIn X Y n) := by
  unfold IsMixedSumIn
  infer_instance

/-- Positive even exceptions to the mixed sumset, up to x. -/
def mixedExcSet (X Y : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun n => Even n ∧ ¬ IsMixedSumIn X Y n)

/-- Page 3 final paragraph, the exceptional-set form of the claimed extension.
This is a statement only, for the withdrawn paper. -/
def MixedTheorem2 : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ →
    ∀ (A B : ℕ → Finset ℕ) (δ₁ δ₂ : ℕ → ℝ),
      IsPrimeFamily A → IsPrimeFamily B →
      DensityFloor δ₁ c₀ → DensityFloor δ₂ c₀ →
      SiegelWalfiszNat A δ₁ → SiegelWalfiszNat B δ₂ →
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
        ((mixedExcSet (A x) (B x) x).card : ℝ) ≤ C * x / Real.log x ^ η

/-- The diagonal mixed exceptional set is the original exceptional set. -/
theorem mixedExcSet_self (X : Finset ℕ) (x : ℕ) :
    mixedExcSet X X x = excSet X x := rfl

end LeanLab.Xi2012.NatEncoding

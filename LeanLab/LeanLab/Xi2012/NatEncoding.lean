import LeanLab.Xi2012.Statements

/-!
Xi 2012, arXiv 1206.2148v1, pages 2 and 3.
AI wrote the Lean code. Binary Goldbach is open.

The binder in thetaNat is explicitly natural. Real casts occur only in the
cutoff and logarithm. The withdrawn main results remain propositions.
Theorem1Printed keeps the whole sumset printed on page 3. Theorem1Even is
its separate even truncated interpretation. Constants follow the family
parameters, as in the existing lab encoding. No main result is asserted.
-/

namespace LeanLab.Xi2012.NatEncoding

open Finset Real

/-- Page 2 before equation 2. Congruence is in the natural numbers. -/
noncomputable def thetaNat (X : Finset ℕ) (y : ℝ) (q a : ℕ) : ℝ := by
  classical
  exact ∑ p ∈ X.filter (fun p : ℕ => (p : ℝ) ≤ y ∧ Nat.ModEq q p a), Real.log p

/-- Page 2 equation 3, with a natural congruence and nonnegative cutoff. -/
def SiegelWalfiszNat (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ c →
    ∀ a : ℕ, Nat.Coprime a q → ∀ y : ℝ, 0 ≤ y → y ≤ x →
      |thetaNat (A x) y q a - δ x * y / (Nat.totient q : ℝ)| ≤
        C * x / Real.log x ^ (2 * c)

/-- Page 3 Theorem 2 at a fixed density exponent. Statement only. -/
def Theorem2At (c₀ : ℝ) : Prop :=
  ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ), IsPrimeFamily A →
    DensityFloor δ c₀ → SiegelWalfiszNat A δ →
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      ((excSet (A x) x).card : ℝ) ≤ C * x / Real.log x ^ η

/-- Page 3 Theorem 2. Statement only. -/
def Theorem2 : Prop := ∀ c₀ : ℝ, 0 < c₀ → Theorem2At c₀

/-- Page 3 Theorem 1 as printed, with the whole sumset. Statement only. -/
def Theorem1Printed : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ),
    IsPrimeFamily A → DensityFloor δ c₀ → SiegelWalfiszNat A δ →
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |((sumset (A x)).card : ℝ) - x / 2| ≤ C * x / Real.log x ^ η

/-- Page 3 claimed equivalence, interpreted using even sums up to x.
This is separate from the printed Theorem 1. Statement only. -/
def Theorem1Even : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ),
    IsPrimeFamily A → DensityFloor δ c₀ → SiegelWalfiszNat A δ →
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |((evenSums (A x) x).card : ℝ) - ((x / 2 : ℕ) : ℝ)| ≤
        C * x / Real.log x ^ η

/-- The explicit encoding agrees with the corrected U-5213 encoding. -/
theorem thetaNat_eq_theta (X : Finset ℕ) (y : ℝ) (q a : ℕ) :
    thetaNat X y q a = LeanLab.Xi2012.theta X y q a := rfl

/-- Compatibility with the corrected lab statements, not the superseded real encoding. -/
theorem encoding_compatibility :
    (∀ A δ, SiegelWalfiszNat A δ ↔ LeanLab.Xi2012.SiegelWalfisz A δ) ∧
    (∀ c₀, Theorem2At c₀ ↔ LeanLab.Xi2012.Theorem2At c₀) ∧
    (Theorem2 ↔ LeanLab.Xi2012.Theorem2) ∧
    (Theorem1Printed ↔ LeanLab.Xi2012.Theorem1Printed) ∧
    (Theorem1Even ↔ LeanLab.Xi2012.Theorem1Even) :=
  ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- The encoding distinguishes residues and respects the real cutoff. -/
theorem thetaNat_residue_sensitive :
    thetaNat {7} 10 3 1 = Real.log 7 ∧
    thetaNat {7} 10 3 2 = 0 ∧
    thetaNat {7} 6 3 1 = 0 ∧
    thetaNat {7} 10 3 1 ≠ thetaNat {7} 10 3 2 := by
  have h₁ : thetaNat {7} 10 3 1 = Real.log 7 := by
    norm_num [thetaNat, Finset.sum_filter, Nat.ModEq]
  have h₂ : thetaNat {7} 10 3 2 = 0 := by
    norm_num [thetaNat, Finset.sum_filter, Nat.ModEq]
  refine ⟨h₁, h₂, ?_, ?_⟩
  · norm_num [thetaNat, Finset.sum_filter, Nat.ModEq]
  · rw [h₁, h₂]
    exact ne_of_gt (Real.log_pos (by norm_num))

end LeanLab.Xi2012.NatEncoding

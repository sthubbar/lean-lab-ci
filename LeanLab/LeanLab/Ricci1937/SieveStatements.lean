import Mathlib

/-!
Ricci 1937, page 81, Theorem I, formulas 3.1 and 3.2.
The estimate is a named input, not a theorem proved in this file.
Its polynomial and parameter data must be justified when constructing an instance.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Ricci's prime indexing starts with p_1 = 2. Only positive indices are used below. -/
def ricciPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- The count A on page 81 for supplied integer values and prime and square thresholds. -/
def ricciSieveCount (F : ℤ → ℤ) (z : ℤ) (ξ u v : ℕ) : ℕ :=
  #{x ∈ Ioc z (z + (ξ : ℤ)) |
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ F x → u < p) ∧
    ∀ d : ℕ, 1 < d → ((d : ℤ) ^ 2) ∣ F x → v < d}

/-- The numerical form of Theorem I, for supplied valid polynomial and parameter data.
The parameter f is the number of irreducible factors. Tau is its value at f.
This Prop records a cited input and asserts no instance of that input. -/
def TheoremIEstimate (F : ℤ → ℤ) (f : ℕ) (τ σ σbar μ : ℝ) : Prop :=
  1 ≤ f ∧ 0 < μ ∧ ∀ ε : ℝ, 0 < ε → ∃ γ : ℕ, 1 ≤ γ ∧
    ∀ t r : ℕ, γ ≤ t → t ≤ r → ∀ z : ℤ, ∀ ξ : ℕ,
      (σbar - ε) * μ * ξ / Real.log (ricciPrime t) ^ f -
          ricciPrime r * (ricciPrime t : ℝ) ^ (2 * τ + ε) < ricciSieveCount F z ξ (ricciPrime t) (ricciPrime r) ∧
      (ricciSieveCount F z ξ (ricciPrime t) (ricciPrime r) : ℝ) <
        (σ + ε) * μ * ξ / Real.log (ricciPrime t) ^ f +
          (ricciPrime r : ℝ) ^ (2 : ℕ) * (ricciPrime t : ℝ) ^ (2 * τ + ε)

/-- Raising either threshold only reduces the survivor count. -/
theorem ricciSieveCount_mono (F : ℤ → ℤ) (z : ℤ) (ξ : ℕ) {u u' v v' : ℕ}
    (hu : u ≤ u') (hv : v ≤ v') :
    ricciSieveCount F z ξ u' v' ≤ ricciSieveCount F z ξ u v := by
  apply card_le_card
  intro x hx
  rcases mem_filter.mp hx with ⟨hxI, hp, hd⟩
  exact mem_filter.mpr ⟨hxI, fun p hprime hdiv => hu.trans_lt (hp p hprime hdiv),
    fun d hd1 hdiv => hv.trans_lt (hd d hd1 hdiv)⟩

example : (1 : ℤ) ∈ Ioc (0 : ℤ) 5 ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ 1 → 1 < p) ∧
    ∀ d : ℕ, 1 < d → (d : ℤ) ^ 2 ∣ 1 → 1 < d := by
  exact ⟨by norm_num, fun p hp _ => hp.one_lt, fun _ hd _ => hd⟩

end
end LeanLab.Ricci1937

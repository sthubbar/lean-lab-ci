import LeanLab.Ricci1937.FormA
import LeanLab.Ricci1937.SieveStatements

/-!
Ricci 1937, page 90, Theorem IV and formula 10.1.
The sieve constants and the theorem remain named inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset Real
noncomputable section

/-- The product of the first v primes, with Ricci's positive indexing. -/
def ricciPrimorial (v : ℕ) : ℕ := ∏ i ∈ Icc 1 v, ricciPrime i

/-- The product rho in Theorem IV. Its convergence is not proved in this file. -/
def ricciRho (v : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ ricciPrime v < p},
    (1 + 1 / ((p.val : ℝ) - 1) ^ (3 : ℕ))

/-- The integer k selected from supplied valid upper sieve constants. -/
def ricciIVK (v : ℕ) (τ₂ σ : ℝ) : ℕ :=
  ⌊(16 / 3 : ℝ) * exp (-2 * Real.eulerMascheroniConstant) * ricciRho v *
    (1 + τ₂) ^ (2 : ℕ) * σ⌋₊ + 1

/-- The partition conclusion of formula 10.1. -/
def RicciPartition (j k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n → ∃ l : List ℕ,
    l.length = 2 * k ∧ (∀ p ∈ l, p.Prime) ∧
      ∃ w : ℕ, w ≤ j * k - 1 ∧ l.sum + w = n

/-- Theorem IV for supplied valid sieve constants. This Prop asserts no instance. -/
def TheoremIVInput (τ₂ σ : ℝ) : Prop :=
  0 ≤ τ₂ ∧ 0 < σ ∧ ∀ v : ℕ, 1 ≤ v → RicciPartition (ricciPrimorial v) (ricciIVK v τ₂ σ)

lemma ricciPrimorial_four : ricciPrimorial 4 = 210 := by
  have hI : Icc (1 : ℕ) 4 = {1, 2, 3, 4} := by decide
  norm_num [ricciPrimorial, hI, ricciPrime, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

/-- The general partition form at the printed j and k is the existing RicciForm. -/
lemma ricciPartition_210_32_iff : RicciPartition 210 32 ↔ RicciForm := by
  norm_num [RicciPartition, RicciForm]

/-- CONDITIONAL ON Theorem IV and the supplied verification of k = 32. -/
theorem ricciForm_of_theoremIV {τ₂ σ : ℝ} (hIV : TheoremIVInput τ₂ σ)
    (hk : ricciIVK 4 τ₂ σ = 32) : RicciForm := by
  have h := hIV.2.2 4 (by norm_num)
  rw [ricciPrimorial_four, hk] at h
  exact ricciPartition_210_32_iff.mp h

end
end LeanLab.Ricci1937

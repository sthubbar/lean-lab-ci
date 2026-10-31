/-
CODEX task79. AI wrote the Lean code. Binary Goldbach is open.
CITED INPUTS, not proved in Lean. Any use is CONDITIONAL ON the named input.
Source: papers/P0075.pdf, Chirre and Hagen 2025, arXiv 2512.23534v1,
printed page 13, Lemma A.1, displays 1, 2 and 3.
Checked line by line against papers/P0075.txt and the rendered PDF page.
The explicit summability clauses prevent divergent sums from taking default value zero.
The independent convergence proofs are in Task79AppendixConvergence.lean.
-/
import Mathlib

namespace LeanLab.Routes.Task79

open scoped BigOperators

/-- CITED INPUT. P0075 page 13, Lemma A.1, displays 1 to 3, with convergence explicit. Not proved here. -/
def AppendixA1 : Prop :=
  let f₁ : Nat.Primes → ℝ := fun p =>
    Real.log ((p : ℕ) : ℝ) / (Real.sqrt ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1))
  let f₂ : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt (n + 1) ^ 2 / (((n + 1 : ℕ) : ℝ) ^ 2)
  let f₃ : Nat.Primes → ℝ := fun p =>
    Real.log ((p : ℕ) : ℝ) ^ 2 / (((p : ℕ) : ℝ) ^ 2 - ((p : ℕ) : ℝ))
  Summable f₁ ∧ (∑' p, f₁ p) < 1.7215 ∧
    Summable f₂ ∧ (∑' n, f₂ n) < 0.8053 ∧
    Summable f₃ ∧ (∑' p, f₃ p) < 0.982

/-- CITED INPUT. P0075 page 13, Lemma A.1, display 1. Not proved in Lean. -/
def appendixA1_prime_sqrt_bound : Prop :=
    (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) /
      (Real.sqrt ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1))) < 1.7215

/-- CITED INPUT. P0075 page 13, Lemma A.1, display 2. Not proved in Lean. -/
def appendixA1_mangoldt_bound : Prop :=
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt (n + 1) ^ 2 /
      (((n + 1 : ℕ) : ℝ) ^ 2)) < 0.8053

/-- CITED INPUT. P0075 page 13, Lemma A.1, display 3. Not proved in Lean. -/
def appendixA1_prime_sq_bound : Prop :=
    (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) ^ 2 /
      (((p : ℕ) : ℝ) ^ 2 - ((p : ℕ) : ℝ))) < 0.982

end LeanLab.Routes.Task79

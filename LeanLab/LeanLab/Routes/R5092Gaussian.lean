/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261019T2314Z-cloud29, unit U-5792, route R-5092.

# Gaussian Goldbach: an even N as a sum of two Gaussian primes off the real axis

`prime_of_norm_prime`: a Gaussian integer whose norm is a rational prime is prime in `ℤ[i]`.
`gauss_rep`: if `a² + b²` and `(N - a)² + b²` are both prime, then
`N = (a + bi) + ((N - a) - bi)` is a sum of two Gaussian primes with nonzero imaginary part.
`ten_rep`: `10 = (4 + i) + (6 - i)`, `17` and `37` prime.

Numerics, Routes/numerics/r5092_gauss.out: every even `N ≤ 20000` already has such a pair with
`b = 1`, that is some `a` with `a² + 1` and `(N - a)² + 1` both prime. The Gaussian problem has
two free variables and many more candidates, but it asks for two prime values of two quadratic
forms at once, so the sieve sees the same parity barrier; and it does not imply rational Goldbach.
KNOWN conjecture, Holben and Jordan 1968. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Routes.R5092
open GaussianInt

/-- A Gaussian integer with prime norm is prime in `ℤ[i]`. -/
theorem prime_of_norm_prime {z : GaussianInt} (h : (Zsqrtd.norm z).natAbs.Prime) : Prime z := by
  apply Irreducible.prime
  refine ⟨?_, ?_⟩
  · intro hu
    rw [← Zsqrtd.norm_eq_one_iff] at hu
    rw [hu] at h; exact Nat.not_prime_one h
  · intro x y hxy
    have hn : (Zsqrtd.norm z).natAbs = (Zsqrtd.norm x).natAbs * (Zsqrtd.norm y).natAbs := by
      rw [hxy, Zsqrtd.norm_mul, Int.natAbs_mul]
    rw [hn] at h
    rcases Nat.prime_mul_iff.mp h with ⟨_, h1⟩ | ⟨_, h1⟩
    · right; exact Zsqrtd.norm_eq_one_iff.mp h1
    · left; exact Zsqrtd.norm_eq_one_iff.mp h1

theorem norm_mk (a b : ℤ) : Zsqrtd.norm (⟨a, b⟩ : GaussianInt) = a ^ 2 + b ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- Gaussian Goldbach from two prime values. -/
theorem gauss_rep (N : ℕ) (a b : ℤ) (hb : b ≠ 0) (h1 : (a ^ 2 + b ^ 2).natAbs.Prime)
    (h2 : (((N : ℤ) - a) ^ 2 + b ^ 2).natAbs.Prime) :
    ∃ π₁ π₂ : GaussianInt, Prime π₁ ∧ Prime π₂ ∧ π₁ + π₂ = (N : GaussianInt) ∧ π₁.im ≠ 0 := by
  refine ⟨⟨a, b⟩, ⟨(N : ℤ) - a, -b⟩, ?_, ?_, ?_, hb⟩
  · apply prime_of_norm_prime; rw [norm_mk]; exact h1
  · apply prime_of_norm_prime; rw [norm_mk, neg_sq]; exact h2
  · ext <;> simp

/-- `10 = (4 + i) + (6 - i)`. -/
theorem ten_rep : ∃ π₁ π₂ : GaussianInt, Prime π₁ ∧ Prime π₂ ∧ π₁ + π₂ = ((10 : ℕ) : GaussianInt) ∧
    π₁.im ≠ 0 :=
  gauss_rep 10 4 1 one_ne_zero (by norm_num) (by norm_num)

end LeanLab.Routes.R5092

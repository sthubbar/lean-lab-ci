/-
Ramaré 1995, On Šnirel'man's constant, Ann. Sc. Norm. Pisa 22, 645-706.
Statements of the main results, plus the deductions the paper makes from them.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
A `sorry` marks a statement taken from the paper and not proved in the lab.
-/
import Mathlib
import LeanLab.SchnirelmannConstant.Defs

open Finset
open scoped Classical

namespace LeanLab.Ramare1995
open LeanLab.SchnirelmannConstant

/-- Paper p. 646: Theorem 1 for even integers above `10^30`, via Deshouillers' effective
Ostmann theorem. Not proved in the lab. -/
theorem large_even : ∀ n : ℕ, Even n → 10 ^ 30 < n → AtMostPrimes 6 n := by
  sorry

/-- Paper p. 646: the remaining even integers, by an ascent process using the author's
effective short interval results. Not proved in the lab. -/
theorem small_even : ∀ n : ℕ, Even n → n ≤ 10 ^ 30 → AtMostPrimes 6 n := by
  sorry

/-- Theorem 1, p. 645: every even integer is a sum of at most 6 primes.
Proved here from `large_even` and `small_even`. -/
theorem theorem1_of (hL : ∀ n : ℕ, Even n → 10 ^ 30 < n → AtMostPrimes 6 n)
    (hS : ∀ n : ℕ, Even n → n ≤ 10 ^ 30 → AtMostPrimes 6 n) :
    ∀ n : ℕ, Even n → AtMostPrimes 6 n := by
  intro n hn
  rcases Nat.lt_or_ge (10 ^ 30) n with h | h
  · exact hL n hn h
  · exact hS n hn h

theorem theorem1 : ∀ n : ℕ, Even n → AtMostPrimes 6 n := theorem1_of large_even small_even

/-- Corollary, p. 645: every integer larger than 1 is a sum of at most 7 primes.
Proved here from Theorem 1 alone, with zero sorry of its own. -/
theorem corollary_of (h1 : ∀ n : ℕ, Even n → AtMostPrimes 6 n) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 7 n := by
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · exact (h1 n he).mono (by norm_num)
  · have h3 : 3 ≤ n := by obtain ⟨k, rfl⟩ := ho; omega
    have hev : Even (n - 3) := by
      obtain ⟨k, rfl⟩ := ho; exact ⟨k - 1, by omega⟩
    have := (AtMostPrimes.prime Nat.prime_three).add (h1 (n - 3) hev)
    rw [show 3 + (n - 3) = n by omega] at this
    exact this.mono (by norm_num)

theorem corollary : ∀ n : ℕ, 1 < n → AtMostPrimes 7 n := corollary_of theorem1

/-- Number of integers in `]X, 2X]` that are sums of two primes. -/
noncomputable def goldbachCount (X : ℝ) : ℕ :=
  #{n ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | IsGoldbachSum n}

/-- Theorem 2, p. 646, WEAK FORM: for `X > exp 67` a positive proportion of `]X, 2X]` are
sums of two primes, with an unspecified constant. The paper's explicit form, `X/5`, is the
cited input of Theorem1.lean. Retired 2026-10-19 by PC run 20261019T1403Z-32628, unit U-1068,
from a `sorry` theorem into this Prop; PROVED unconditional, with an ineffective constant, as
`LeanLab.Ramare1995.Theorem2Weak.theorem2_weak` in Theorem2Weak.lean. -/
def theorem2_weak_stmt : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ X : ℝ, Real.exp 67 < X → c * X ≤ goldbachCount X

end LeanLab.Ramare1995

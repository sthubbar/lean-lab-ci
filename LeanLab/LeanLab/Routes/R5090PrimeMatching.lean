/-
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T2314Z-cloud29, unit U-5753, route R-5090.

# Prime-sum permutations: what Bertrand gives and what Goldbach asks

`prime_sum_perm`: for every `n` there is a permutation `σ` of `{1, …, n}` with `i + σ(i)` prime
for every `i`. Proof by Bertrand's postulate alone: take a prime `p` with `n < p ≤ 2n`, pair
`i ↔ p - i` on `[p - n, n]`, and recurse on `[1, p - n - 1]`. KNOWN, Greenfield and Greenfield,
J. Integer Sequences 1998. The sums `i + σ(i)` run over several primes.

Binary Goldbach for an even `N` is the one-reflection case: the reflection `i ↦ N - i` of
`[1, N - 1]` has some `i` with both `i` and `N - i` prime. `goldbach_iff_reflection` states it in
this language. The route's barrier: Bertrand fixes the partner `p - i` through the sum, never the
primality of both parts, so no sieve and no parity question arise, and none of Goldbach's
content is reached. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.Routes.R5090
open Finset

/-- For every `n` there is `σ` mapping `[1, n]` injectively into itself, so a permutation, with
every `i + σ(i)` prime. -/
theorem prime_sum_perm (n : ℕ) :
    ∃ σ : ℕ → ℕ, (∀ i ∈ Icc 1 n, σ i ∈ Icc 1 n) ∧ Set.InjOn σ (Icc 1 n : Set ℕ) ∧
      ∀ i ∈ Icc 1 n, (i + σ i).Prime := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨id, by simp, by simp, by simp⟩
    obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
    set m := p - n - 1 with hm
    have hmn : m < n := by omega
    obtain ⟨τ, hτ1, hτ2, hτ3⟩ := ih m hmn
    refine ⟨fun i => if i ≤ m then τ i else p - i, ?_, ?_, ?_⟩
    · intro i hi
      simp only [mem_Icc] at hi ⊢
      split_ifs with h
      · have := hτ1 i (by simp only [mem_Icc]; omega)
        simp only [mem_Icc] at this; omega
      · omega
    · intro i hi j hj hij
      simp only [coe_Icc, Set.mem_Icc] at hi hj
      simp only at hij
      split_ifs at hij with h1 h2 h2
      · exact hτ2 (by simp only [coe_Icc, Set.mem_Icc]; omega)
          (by simp only [coe_Icc, Set.mem_Icc]; omega) hij
      · have := hτ1 i (by simp only [mem_Icc]; omega)
        simp only [mem_Icc] at this; omega
      · have := hτ1 j (by simp only [mem_Icc]; omega)
        simp only [mem_Icc] at this; omega
      · omega
    · intro i hi
      simp only [mem_Icc] at hi
      simp only
      split_ifs with h
      · exact hτ3 i (by simp only [mem_Icc]; omega)
      · rwa [show i + (p - i) = p by omega]

/-- Binary Goldbach for even `N ≥ 4` in reflection form: some `i ∈ [1, N - 1]` with `i` and its
reflection `N - i` both prime. -/
theorem goldbach_iff_reflection (N : ℕ) :
    IsGoldbachSum N ↔ ∃ i ∈ Icc 1 (N - 1), i.Prime ∧ (N - i).Prime := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨p, ?_, hp, by rwa [Nat.add_sub_cancel_left]⟩
    simp only [mem_Icc]; have := hp.two_le; have := hq.two_le; omega
  · rintro ⟨i, hi, hp, hq⟩
    simp only [mem_Icc] at hi
    exact ⟨i, N - i, hp, hq, by omega⟩

/-- The Bertrand construction never uses a single reflection for `n ≥ 3`: a permutation of
`[1, n]` with all `i + σ(i)` equal to one prime `p` forces `σ(i) = p - i`, so `p = n + 1`.
Here the easy half: if `n + 1` is prime the reflection works. -/
theorem one_prime_perm {n : ℕ} (hp : (n + 1).Prime) :
    (∀ i ∈ Icc 1 n, n + 1 - i ∈ Icc 1 n) ∧ ∀ i ∈ Icc 1 n, (i + (n + 1 - i)).Prime := by
  constructor
  · intro i hi; simp only [mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [mem_Icc] at hi; rwa [show i + (n + 1 - i) = n + 1 by omega]

/-- Two primes suffice in interval form when `n + q` is prime for a prime `q ≤ n + 1`: reflect
`[1, q - 1]` by `q` and `[q, n]` by `n + q`. For even `n` this is `n = p - q` with `q ≤ n + 1`,
a binary prime problem with the parity barrier, unlike Bertrand's step. -/
theorem two_prime_perm {n q : ℕ} (hq : q.Prime) (hqn : q ≤ n + 1) (hp : (n + q).Prime) :
    ∃ σ : ℕ → ℕ, (∀ i ∈ Icc 1 n, σ i ∈ Icc 1 n) ∧ Set.InjOn σ (Icc 1 n : Set ℕ) ∧
      ∀ i ∈ Icc 1 n, i + σ i = q ∨ i + σ i = n + q := by
  have hq2 := hq.two_le
  refine ⟨fun i => if i < q then q - i else n + q - i, ?_, ?_, ?_⟩
  · intro i hi; simp only [mem_Icc] at hi ⊢; split_ifs <;> omega
  · intro i hi j hj hij
    simp only [coe_Icc, Set.mem_Icc] at hi hj
    simp only at hij
    split_ifs at hij <;> omega
  · intro i hi; simp only [mem_Icc] at hi; simp only; split_ifs <;> omega

end LeanLab.Routes.R5090

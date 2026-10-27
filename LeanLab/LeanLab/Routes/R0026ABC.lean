/-
# R-0026, T3 MOONSHOT: the abc conjecture cannot see a Goldbach pair

Unit U-1210, PC run 20261020T0902Z-22676.

Route: the abc conjecture and its proven weak forms, Stewart-Yu, bound `c` in a coprime triple
`a + b = c` by a power of `rad(abc)`. Ask whether radical information about `N` could force a
representation `N = p + q`.

The barrier, PROVED here: for distinct primes `p ≠ q`, `N = p + q` satisfies `N ≤ pq ≤ rad(pqN)`,
so the abc quality `log N / log rad(pqN)` is below 1 for every Goldbach triple: they are never
abc hits, and every abc-type theorem, proved or conjectured, is an UPPER bound on `c` that such
triples meet trivially. abc constrains sums of numbers with small radical; primes have the
largest possible radical, so the abc machinery is blind to them.
* `add_le_mul`: `p + q ≤ pq` for `p, q ≥ 2`.
* `mul_le_rad`: for distinct primes `p ≠ q` and `N ≠ 0`, `pq ≤ rad(pqN)`, `rad` the product of the
  distinct prime factors.
* `goldbach_triple_le_rad`: `p + q ≤ rad(pq(p + q))`.

Numerics, Routes/numerics/r0026_abc.out: over every coprime Goldbach triple `p + q = N`, `p ≠ q`,
`N ≤ 2·10^5`, the largest quality is 0.844, at `3 + 16381 = 16384 = 2^14`, the case where `N`
itself has the smallest radical.

KNOWN territory; nothing claimed new. AI wrote this Lean code. Binary Goldbach is OPEN; this route
is a barrier map, not progress.
-/
import Mathlib

namespace LeanLab.Routes.R0026

/-- `rad n`, the product of the distinct primes dividing `n`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem add_le_mul {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) : p + q ≤ p * q := by nlinarith

/-- **`mul_le_rad`**: for distinct primes `p ≠ q` and `N ≠ 0`, `pq ≤ rad(pqN)`. -/
theorem mul_le_rad {p q N : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hN : N ≠ 0) :
    p * q ≤ rad (p * q * N) := by
  unfold rad
  have hne : p * q * N ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero hp.ne_zero hq.ne_zero) hN
  have hsub : ({p, q} : Finset ℕ) ⊆ (p * q * N).primeFactors := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rw [Nat.mem_primeFactors]
    rcases hr with rfl | rfl
    · exact ⟨hp, ⟨q * N, by ring⟩, hne⟩
    · exact ⟨hq, ⟨p * N, by ring⟩, hne⟩
  have h1 : ∏ r ∈ ({p, q} : Finset ℕ), r = p * q := by
    rw [Finset.prod_pair hpq]
  calc p * q = ∏ r ∈ ({p, q} : Finset ℕ), r := h1.symm
    _ ≤ ∏ r ∈ (p * q * N).primeFactors, r :=
      Finset.prod_le_prod_of_subset_of_one_le' hsub fun r hr _ =>
        (Nat.prime_of_mem_primeFactors hr).one_lt.le

/-- **`goldbach_triple_le_rad`**: for distinct primes, `p + q ≤ rad(pq(p + q))`: the abc quality
of a Goldbach triple is at most 1. -/
theorem goldbach_triple_le_rad {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    p + q ≤ rad (p * q * (p + q)) :=
  (add_le_mul hp.two_le hq.two_le).trans (mul_le_rad hp hq hpq (by have := hp.two_le; omega))

/-- Vacuity: the hypotheses of `mul_le_rad` hold at `p = 3`, `q = 5`, `N = 8`. -/
example : 3 * 5 ≤ rad (3 * 5 * 8) := mul_le_rad (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end LeanLab.Routes.R0026

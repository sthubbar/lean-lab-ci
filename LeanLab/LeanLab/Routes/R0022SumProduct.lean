import Mathlib

/-!
# R-0022 The sum-product route: primes are a multiplicative Sidon set, and that says nothing
about P + P

Route R-0022, unit U-1184, PC run 20261020T0603Z-352. AI wrote this Lean code.

Sum-product inequalities, Erdős-Szemerédi, say a finite set A of integers has
|A + A| + |A · A| ≥ |A|^{1+c}: a set with small product set has a large sumset. The route asks
whether the multiplicative structure of the primes forces P + P to be large, all even numbers.

* `prime_mul_eq`: p q = p' q' for primes forces {p, q} = {p', q'}. So every set of primes is a
  multiplicative Sidon set, |A · A| = |A|(|A| + 1)/2, the largest possible: the product side of
  every sum-product inequality is already satisfied and the inequality gives nothing for A + A.
* `delete_kills`, `delete_subset`: for any set A and any N, removing from A each a ≤ N/2 with
  N - a ∈ A leaves a subset with no representation a + b = N; the subset of a set of primes is
  still a set of primes, so still multiplicatively Sidon. No statement that sees only the
  multiplicative structure of a set of primes can give binary Goldbach for one N.

Binary Goldbach itself is OPEN; this file proves nothing about it.
-/

namespace LeanLab.Routes.R0022

/-- Unique factorization for products of two primes. -/
theorem prime_mul_eq {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime)
    (hq' : q'.Prime) (h : p * q = p' * q') :
    (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
  have hdvd : p ∣ p' * q' := ⟨q, h.symm⟩
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · have e1 : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp').mp h1
    subst e1
    left
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos h⟩
  · have e1 : p = q' := (Nat.prime_dvd_prime_iff_eq hp hq').mp h1
    subst e1
    right
    refine ⟨rfl, ?_⟩
    have : p * q = p * p' := by rw [h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hp.pos this

/-- The deletion: drop every `a ≤ N/2` whose partner `N - a` is in `A`. -/
def delete (A : Set ℕ) (N : ℕ) : Set ℕ := {a | a ∈ A ∧ ¬ (2 * a ≤ N ∧ N - a ∈ A)}

theorem delete_subset (A : Set ℕ) (N : ℕ) : delete A N ⊆ A := fun _ h => h.1

/-- After the deletion, `N` has no representation as a sum of two elements. -/
theorem delete_kills (A : Set ℕ) (N : ℕ) :
    ¬ ∃ a ∈ delete A N, ∃ b ∈ delete A N, a + b = N := by
  rintro ⟨a, ha, b, hb, hab⟩
  rcases le_total (2 * a) N with h | h
  · exact ha.2 ⟨h, by rw [show N - a = b by omega]; exact hb.1⟩
  · have h2 : 2 * b ≤ N := by omega
    exact hb.2 ⟨h2, by rw [show N - b = a by omega]; exact ha.1⟩

/-- The deleted set of primes is still a set of primes, hence still multiplicatively Sidon. -/
theorem delete_primes {A : Set ℕ} (hA : ∀ a ∈ A, a.Prime) (N : ℕ) :
    ∀ a ∈ delete A N, a.Prime := fun a ha => hA a ha.1

/-- Vacuity: the hypotheses hold at `2 · 3 = 3 · 2`, and the deletion is not trivial:
for `A` the primes and `N = 10`, `3` is deleted, `7` survives. -/
example : (2 * 3 = 3 * 2) ∧ 3 ∉ delete {p | p.Prime} 10 ∧ 7 ∈ delete {p | p.Prime} 10 := by
  refine ⟨rfl, fun h => h.2 ⟨by norm_num, by norm_num⟩, ⟨by norm_num, fun h => by omega⟩⟩

end LeanLab.Routes.R0022

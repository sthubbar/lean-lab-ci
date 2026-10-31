import Mathlib

/-!
Xi 2012, arXiv 1206.2148v1, page 7 definition of B.
This unbounded predicate isolates the prime-divisor condition before the cutoff.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

/-- Page 7 divisor condition. A is assumed prime in the factorization lemma. -/
def HasPrimeDivisorIn (A : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p ∈ A, p ∣ n

/-- The factorization step behind the decompositions on pages 8 and 9. -/
theorem hasPrimeDivisorIn_mul_iff (A : Finset ℕ)
    (hA : ∀ p ∈ A, Nat.Prime p) (m n : ℕ) :
    HasPrimeDivisorIn A (m * n) ↔ HasPrimeDivisorIn A m ∨ HasPrimeDivisorIn A n := by
  constructor
  · rintro ⟨p, hp, hdiv⟩
    rcases (hA p hp).dvd_mul.mp hdiv with hm | hn
    · exact Or.inl ⟨p, hp, hm⟩
    · exact Or.inr ⟨p, hp, hn⟩
  · rintro (⟨p, hp, hm⟩ | ⟨p, hp, hn⟩)
    · exact ⟨p, hp, dvd_mul_of_dvd_left hm n⟩
    · exact ⟨p, hp, dvd_mul_of_dvd_right hn m⟩

/-- A prime is in the divisor closure precisely when it is selected. -/
theorem hasPrimeDivisorIn_prime_iff (A : Finset ℕ)
    (hA : ∀ p ∈ A, Nat.Prime p) {n : ℕ} (hn : Nat.Prime n) :
    HasPrimeDivisorIn A n ↔ n ∈ A := by
  constructor
  · rintro ⟨p, hp, hdiv⟩
    have heq : p = n := (Nat.prime_dvd_prime_iff_eq (hA p hp) hn).mp hdiv
    simpa only [heq] using hp
  · intro hmem
    exact ⟨n, hmem, dvd_rfl⟩

end LeanLab.Xi2012.NatEncoding

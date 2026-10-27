/-
P0006, page 3, Section 4, sieving the progression k times 2 to the power n plus one.
These statements describe the residue test and preservation of primes above the
cutoff. They do not reproduce the computation. AI wrote the Lean code.
Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.HelfgottPlatt.Task98

/-- Page 3, Section 4. The forbidden coefficient class for an odd prime q. -/
def sieveResidue (q n : ℕ) : ZMod q := -((2 : ZMod q) ^ n)⁻¹

/-- Page 3, Section 4. An odd prime q divides a progression term exactly when
its coefficient belongs to the forbidden residue class. -/
theorem sieve_dvd_iff {q k n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ k * 2 ^ n + 1 ↔ (k : ZMod q) = sieveResidue q n := by
  have : Fact q.Prime := ⟨hq⟩
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd)
  have hpow : (2 : ZMod q) ^ n ≠ 0 := pow_ne_zero _ htwo
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  unfold sieveResidue
  rw [← neg_one_mul (((2 : ZMod q) ^ n)⁻¹), eq_mul_inv_iff_mul_eq₀ hpow]
  constructor <;> intro h <;> linear_combination h

/-- Page 3, Section 4. Sieving by prime divisors strictly below B preserves
every prime N at least B. The cutoff condition prevents removing a prime itself. -/
theorem prime_survives_sieve {N B : ℕ} (hp : N.Prime) (hB : B ≤ N) :
    ∀ q : ℕ, q.Prime → q < B → ¬ q ∣ N := by
  intro q hq hqB hdiv
  rcases hp.eq_one_or_self_of_dvd q hdiv with h | h
  · exact hq.ne_one h
  · omega

/-- Page 3, Section 4. A coefficient in the forbidden class certifies
compositeness when the sieve prime is strictly smaller than the candidate. -/
theorem not_prime_of_sieve {q k n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hsmall : q < k * 2 ^ n + 1) (hr : (k : ZMod q) = sieveResidue q n) :
    ¬ (k * 2 ^ n + 1).Prime := by
  intro hp
  have hd := (sieve_dvd_iff hq hq2).mpr hr
  exact prime_survives_sieve hp (B := q + 1) (by omega) q hq (by omega) hd

/-- Page 3, vacuity instances. The residue class removes 33 using q = 3,
while the prime 17 survives the sieve with cutoff 10. -/
theorem sieve_instances :
    sieveResidue 3 4 = 2 ∧ ¬ (33 : ℕ).Prime ∧
      ∀ q : ℕ, q.Prime → q < 10 → ¬ q ∣ 17 := by
  refine ⟨by decide +kernel, ?_, prime_survives_sieve (by decide) (by decide)⟩
  simpa using not_prime_of_sieve (q := 3) (k := 2) (n := 4)
    (by decide) (by decide) (by decide) (by decide +kernel)

end LeanLab.HelfgottPlatt.Task98

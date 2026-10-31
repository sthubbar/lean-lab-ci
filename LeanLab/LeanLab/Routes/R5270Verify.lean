/-
R-5270 VERIFY, PC 20261020T2004Z-7678, unit U-1286, T3.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

Corrections to the gloss of R5270.lean, which is left unchanged.
* `prime_dvd_le_of_ne_zero`: if res A N ≠ 0 and A ⊆ [0, N], every prime
  factor of res A N is at most N.  So a nonzero resultant is made entirely
  of primes ≤ N, counted with multiplicity.
* `two_pow_dvd_res`: if N is even and every a ∈ A is odd, then
  2 ^ (|A|²) ∣ res A N.  Prime power data at the single prime 2 already
  carries about |A|² log 2 of the |A|² log N size, far more than the
  primorial bound N log 4 used in `small_primes_too_small`, which only
  covers squarefree divisors.
* `prime_pow_certificate`: ℓ ^ k ∣ res A N with ℓ ^ k > N ^ (|A|²) forces a
  representation; certificates can be prime powers of small primes, and the
  barrier is the size of the exponent, not the size of ℓ.
-/
import Mathlib
import LeanLab.Routes.R5270

namespace LeanLab.Routes.R5270Verify

open Finset LeanLab.Routes.R5270

theorem prime_dvd_le_of_ne_zero (A : Finset ℕ) (N ℓ : ℕ) (hℓ : ℓ.Prime)
    (hA : ∀ a ∈ A, a ≤ N) (h0 : res A N ≠ 0) (hd : (ℓ : ℤ) ∣ res A N) :
    ℓ ≤ N := by
  by_contra hle
  have hlt : N < ℓ := Nat.lt_of_not_le hle
  have := (large_prime_dvd_iff A N ℓ hℓ hA hlt).mp hd
  exact h0 ((res_eq_zero_iff A N).mpr this)

theorem two_pow_dvd_res (A : Finset ℕ) (N : ℕ) (hN : Even N)
    (hA : ∀ a ∈ A, Odd a) : (2 : ℤ) ^ (A.card ^ 2) ∣ res A N := by
  unfold res
  have hfac : ∀ a ∈ A, ∀ b ∈ A, (2 : ℤ) ∣ ((N : ℤ) - a - b) := by
    intro a ha b hb
    obtain ⟨n, hn⟩ := hN
    obtain ⟨x, hx⟩ := hA a ha
    obtain ⟨y, hy⟩ := hA b hb
    refine ⟨(n : ℤ) - x - y - 1, ?_⟩
    subst hn hx hy
    push_cast
    ring
  have hrow : ∀ a ∈ A, (2 : ℤ) ^ A.card ∣ ∏ b ∈ A, ((N : ℤ) - a - b) := by
    intro a ha
    have := Finset.prod_dvd_prod_of_dvd (s := A) (fun _ => (2 : ℤ))
      (fun b => ((N : ℤ) - a - b)) (fun b hb => hfac a ha b hb)
    simpa [Finset.prod_const] using this
  have := Finset.prod_dvd_prod_of_dvd (s := A) (fun _ => (2 : ℤ) ^ A.card)
    (fun a => ∏ b ∈ A, ((N : ℤ) - a - b)) hrow
  simpa [Finset.prod_const, ← pow_mul, sq] using this

theorem prime_pow_certificate (A : Finset ℕ) (N ℓ k : ℕ) (hA : ∀ a ∈ A, a ≤ N)
    (hd : ((ℓ ^ k : ℕ) : ℤ) ∣ res A N) (hbig : N ^ (A.card ^ 2) < ℓ ^ k) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = N :=
  crt_certificate A N (ℓ ^ k) hA hd hbig

/-- Vacuity: A = {3, 5}, N = 12 is a fake set, no representation, and the
hypotheses of `two_pow_dvd_res` hold; res = 6·4·4·2 = 192, divisible by
2 ^ 4, indeed by 2 ^ 6. -/
example : res {3, 5} 12 ≠ 0 ∧ res {3, 5} 12 = 192 ∧ (2 : ℤ) ^ 6 ∣ res {3, 5} 12 := by
  refine ⟨by decide, by decide, by decide⟩

example : (2 : ℤ) ^ (({3, 5} : Finset ℕ).card ^ 2) ∣ res {3, 5} 12 :=
  two_pow_dvd_res {3, 5} 12 ⟨6, rfl⟩ (by decide)

end LeanLab.Routes.R5270Verify

#print axioms LeanLab.Routes.R5270Verify.prime_dvd_le_of_ne_zero
#print axioms LeanLab.Routes.R5270Verify.two_pow_dvd_res
#print axioms LeanLab.Routes.R5270Verify.prime_pow_certificate

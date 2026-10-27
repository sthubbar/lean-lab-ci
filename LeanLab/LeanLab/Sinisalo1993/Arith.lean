/-
P0041 Sinisalo 1993, Sections 2 and 4: the sieve bookkeeping and the ternary remark, checked
in Lean. Run 20261018T1103Z-12430, unit U-0940. Every statement PROVED, zero sorry.
AI-written Lean code, Claude, 2026-10-18. Ternary Goldbach is a theorem of Helfgott; binary
Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Richstein2001.Remark

namespace LeanLab.Sinisalo1993

open LeanLab

/-- Section 2: the bit table of the primes up to 1048576 = 2^20 has 32768 = 2^20 / 32 words. -/
theorem table_size : (1048576 : ℕ) = 2 ^ 20 ∧ 1048576 / 32 = 32768 := by norm_num

/-- Section 2: primes up to 2^20 sieve every interval up to 2^40, about 1.0995·10^12. -/
theorem sieve_reach : (2 : ℕ) ^ 20 * 2 ^ 20 = 2 ^ 40 ∧ 2 ^ 40 = 1099511627776 ∧
    10995 * 10 ^ 8 < 2 ^ 40 ∧ 2 ^ 40 < 10996 * 10 ^ 8 := by norm_num

/-- Any composite m below 2^40 has a prime factor at most 2^20. -/
theorem small_factor {m : ℕ} (hm : m < 2 ^ 40) (h2 : 2 ≤ m) (hc : ¬ m.Prime) :
    ∃ q, q.Prime ∧ q ∣ m ∧ q ≤ 2 ^ 20 := by
  refine ⟨m.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd m, ?_⟩
  have h := Nat.minFac_sq_le_self (by omega) hc
  by_contra hq
  push_neg at hq
  have : 2 ^ 40 < m.minFac ^ 2 := by
    calc (2 : ℕ) ^ 40 = (2 ^ 20) ^ 2 := by norm_num
      _ < m.minFac ^ 2 := Nat.pow_lt_pow_left hq (by norm_num)
  omega

/-- Section 2: the basic step 2^2·3·5·7·11·13·17 = 1021020. -/
theorem step_size : 2 ^ 2 * 3 * 5 * 7 * 11 * 13 * 17 = (1021020 : ℕ) := by norm_num

/-- Section 4: if even Goldbach holds up to M and some prime p lies in (N - M, N - 2) with
N ≥ M + 3 odd, then N is a sum of three primes. -/
theorem remark {M N p : ℕ} (hE : EvenGoldbachUpTo M) (hN : Odd N) (hNM : M + 3 ≤ N)
    (hp : p.Prime) (h1 : N - M < p) (h2 : p < N - 2) : IsTernarySum N := by
  have hp2 : p ≠ 2 := by omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have h4 : p + 4 ≤ N := by
    obtain ⟨a, ha⟩ := hN
    obtain ⟨b, hb⟩ := hpo
    omega
  exact Richstein2001.ternary_of_prime_near hE hN hp hp2 h4 (by omega)

end LeanLab.Sinisalo1993

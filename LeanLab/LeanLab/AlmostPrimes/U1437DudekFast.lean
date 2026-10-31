import LeanLab.AlmostPrimes.DudekFrom1e9
import LeanLab.Verifications.U1437Fast.Sieve

/-!
# Dudek 2017, every integer `N > 2` is a prime plus a square-free number, P0048 I-5067

Unit U-1437, run 20261021T1603Z-28836, T1. AI wrote the Lean code. KNOWN mathematics, Dudek 2017
Theorem 1, arXiv 1410.7459. Goldbach itself is OPEN.

The finite part is `SqfUpTo B` of `Verifications.U1437Fast.Sieve`: every `N` with `3 ≤ N ≤ B`,
odd or even, is `p + (N - p)` with `p < N` prime and `N - p` square-free. It replaces the even
Goldbach check to `10⁹` of `DudekFrom1e9.dudek_even_of_1e9`, which is far stronger than Dudek's
theorem needs and costs the 1011 Goldbach windows of `Top50/BitUpTo1e9`.

* `dudek_even_of_sqf`: every even `N ≥ 4`, from `SqfUpTo (10^9)` and the lab's analytic
  `dudek_even_from_1e9`, so no Goldbach check is in the closure.
* `dudek_all_of_sqf`: every `N > 2`, CONDITIONAL ON `DudekOddFrom (10^9)`, Dudek's statement for
  odd `N > 10⁹`. The lab's Brun-Titchmarsh and Chebyshev route gives the even half only: for odd
  `N` the prime `p` must lie in the class `N - 2 mod 4`, which needs an explicit lower bound for
  primes in a class mod 4; Dudek uses Ramaré-Rumely for moduli `a² ≤ 169`.
-/

namespace LeanLab.AlmostPrimes.U1437DudekFast

open LeanLab.Verifications.U1437Fast LeanLab.Verifications.Top50.Bits

/-- The paper's form: `N = p + m`, `p` prime, `m ≥ 1` square-free, stated as `p < N` and
`Squarefree (N - p)`. -/
def DudekAt (N : ℕ) : Prop := ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p)

/-- Dudek's theorem for odd `N > X`, the named analytic input of the odd half. -/
def DudekOddFrom (X : ℕ) : Prop := ∀ N : ℕ, Odd N → X < N → DudekAt N

theorem dudekAt_iff (N : ℕ) :
    DudekAt N ↔ ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  constructor
  · rintro ⟨p, hp, hpN, hs⟩
    exact ⟨p, N - p, hp, by omega, hs, by omega⟩
  · rintro ⟨p, m, hp, hm, hs, rfl⟩
    exact ⟨p, hp, by omega, by simpa using hs⟩

/-- Even `N ≥ 10⁹`, the lab's analytic part, as `DudekAt`. -/
theorem dudekAt_even_large (N : ℕ) (hE : Even N) (hN : 10 ^ 9 ≤ N) : DudekAt N :=
  (dudekAt_iff N).mpr
    (DudekFrom1e9.dudek_even_from_1e9 N hE (by exact_mod_cast hN))

/-- **Every even `N ≥ 4` is a prime plus a positive square-free number, from `SqfUpTo (10^9)`.**
The finite input is the square-free window chain, not a Goldbach check. -/
theorem dudek_even_of_sqf (h : SqfUpTo (10 ^ 9)) (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  rw [← dudekAt_iff]
  by_cases hN : N ≤ 10 ^ 9
  · exact h N (by omega) hN
  · exact dudekAt_even_large N hE (by omega)

/-- **Dudek 2017 Theorem 1, every `N > 2`, CONDITIONAL ON `DudekOddFrom (10^9)`**, given the
finite check `SqfUpTo (10^9)`, which covers odd and even `N ≤ 10⁹`. -/
theorem dudek_all_of_sqf (h : SqfUpTo (10 ^ 9)) (hodd : DudekOddFrom (10 ^ 9)) :
    ∀ N : ℕ, 2 < N → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) := by
  intro N hN
  by_cases hs : N ≤ 10 ^ 9
  · exact h N (by omega) hs
  · rcases Nat.even_or_odd N with hE | hO
    · exact dudekAt_even_large N hE (by omega)
    · exact hodd N hO (by omega)

/-- Vacuity of `DudekOddFrom (10^9)`: its conclusion holds at the first odd `N` it covers,
`N = 10⁹ + 1`, by one kernel window. -/
theorem check_1e9p1 :
    tm 999999948 1000000001 1000000001 &&&
      gm (sfm 999999948 53) (LeanLab.Verifications.Top50.P10k.take 16) =
    tm 999999948 1000000001 1000000001 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dudekAt_1e9p1 : DudekAt (10 ^ 9 + 1) := by
  have h := sqf_of_wcheck (lo := 999999948) (W := 53) (A := 1000000001) (B := 1000000001)
    (by norm_num) (by norm_num [BB]) (by norm_num) q16_prime check_1e9p1
  rw [show (10 : ℕ) ^ 9 + 1 = 1000000001 by norm_num]
  exact h 1000000001 le_rfl le_rfl

end LeanLab.AlmostPrimes.U1437DudekFast

#print axioms LeanLab.AlmostPrimes.U1437DudekFast.dudek_even_of_sqf
#print axioms LeanLab.AlmostPrimes.U1437DudekFast.dudek_all_of_sqf
#print axioms LeanLab.AlmostPrimes.U1437DudekFast.dudekAt_1e9p1
#print axioms LeanLab.Verifications.U1437Fast.sqfUpTo_1e4

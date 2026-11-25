import Mathlib

/-!
Route burst S128, burst-20261122. Split of the EASY LEAF `PVCases1122.odd_small`, Pomerance
2011 Theorem 1, odd case, for the moduli q below 7 left out of `odd_truncated`, into one
LEAF per modulus. q = 0 is excluded by NeZero, q = 1 by hypothesis, and q = 2 has no odd
character since -1 = 1 in ZMod 2; that case is PROVED in `PVCases1122.odd_small`.
Each LEAF is a finite check over one period: the initial segment sums of an odd primitive
character mod q have norm at most sqrt 2, so an interval sum, a difference of two of them,
has norm at most 2 sqrt 2, against a bound above 2.08 for q = 3, above 2.65 for q = 4 and
above 3.14 for q = 5. Mod 6 there is no primitive character.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddSmallS128

open Real Finset

/-- LEAF: Pomerance 2011 Theorem 1, odd case, the modulus q = 3, one case of
`PVCases1122.odd_small`. The odd character mod 3 is the Legendre symbol, with initial segment sums 0 and 1. Class EASY. -/
theorem odd_small_q3 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqk : q = 3) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

/-- LEAF: Pomerance 2011 Theorem 1, odd case, the modulus q = 4, one case of
`PVCases1122.odd_small`. The odd character mod 4 takes 1, 0, -1, 0, with initial segment sums 0 and 1. Class EASY. -/
theorem odd_small_q4 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqk : q = 4) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

/-- LEAF: Pomerance 2011 Theorem 1, odd case, the modulus q = 5, one case of
`PVCases1122.odd_small`. An odd character mod 5 has chi 2 equal to i or -i, so its initial segment sums are 0, 1, 1 + chi 2 and 1, of norm at most sqrt 2. Class EASY. -/
theorem odd_small_q5 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqk : q = 5) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

/-- LEAF: Pomerance 2011 Theorem 1, odd case, the modulus q = 6, one case of
`PVCases1122.odd_small`. There is no primitive character mod 6, since every character mod 6 is induced from one mod 3, so the hypotheses are contradictory. Class EASY. -/
theorem odd_small_q6 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqk : q = 6) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

end LeanLab.HelfgottMajor.PVOddSmallS128

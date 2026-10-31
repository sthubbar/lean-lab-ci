/-
P0041 Sinisalo 1993, Section 4: the ternary consequence of the even check combined with
Young and Potler's maximal prime gap 778 below 7.263·10^13, the one Section 4 input the
folder had left unstated. Run PC 20261021T0703Z-4724, unit U-1380.

The gap input is reused, not restated: `Kaniecki1995.YoungPotler`, `λ(7.263·10^13) ≤ 778`,
every prime `p ≤ 7.263·10^13` has `nextPrime p - p ≤ 778`. It stays CITED.

* `ternary_upto_YP`: odd `7 ≤ N ≤ 7.263·10^13` is a sum of three primes, CONDITIONAL ON
  YoungPotler only; even Goldbach to 1000, kernel checked in Common, replaces Sinisalo's
  4·10^11 on this range.
* `ternary_upto_YP_S`: odd `7 ≤ N ≤ 7.263·10^13 + 4·10^11 - 1000` is a sum of three
  primes, CONDITIONAL ON YoungPotler and Sinisalo's even check to 4·10^11; here the
  4·10^11 is really used, through the Section 4 `remark` route.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Ternary Goldbach is a theorem of Helfgott; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Common.GoldbachSmall
import LeanLab.Kaniecki1995.Statements
import LeanLab.Richstein2001.Remark

namespace LeanLab.Sinisalo1993.Ternary

open LeanLab LeanLab.Kaniecki1995

theorem nextPrime_spec' (p : ℕ) : p + 1 ≤ nextPrime p ∧ (nextPrime p).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (p + 1))

/-- Helper, a copy of Kaniecki1995 `gap_le_lam`: a prime `p ≤ x` has gap at most `λ(x)`. -/
theorem gap_le_lam' {x : ℝ} (hx : 7 < x) {p : ℕ} (hp : p.Prime) (hpx : (p : ℝ) ≤ x) :
    nextPrime p - p ≤ lam x := by
  unfold lam
  rw [if_neg (by linarith)]
  apply Finset.le_sup (f := fun p => nextPrime p - p)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpx), hp⟩

/-- Helper: under Young-Potler every prime `p ≤ 7.263·10^13` has `nextPrime p ≤ p + 778`. -/
theorem yp_next (hYP : YoungPotler) {p : ℕ} (hp : p.Prime) (hle : p ≤ 72630000000000) :
    nextPrime p ≤ p + 778 := by
  have h := gap_le_lam' (x := 72630000000000) (by norm_num) hp (by exact_mod_cast hle)
  have h' : lam 72630000000000 ≤ 778 := by
    have h0 := hYP; unfold YoungPotler at h0; exact_mod_cast h0
  have := (nextPrime_spec' p).1
  omega

/-- Helper: for `3 ≤ y ≤ 7.263·10^13` the largest prime `p ≤ y` is odd and `p + 778 > y`. -/
theorem big_prime_below (hYP : YoungPotler) {y : ℕ} (h3 : 3 ≤ y) (hy : y ≤ 72630000000000) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ p ≤ y ∧ y < p + 778 := by
  classical
  set p := Nat.findGreatest Nat.Prime y with hpdef
  have hpP : p.Prime := Nat.findGreatest_spec (m := 3) h3 Nat.prime_three
  have hp3 : 3 ≤ p := Nat.le_findGreatest h3 Nat.prime_three
  have hpy : p ≤ y := Nat.findGreatest_le y
  obtain ⟨hn1, hn2⟩ := nextPrime_spec' p
  have hny : y < nextPrime p := by
    by_contra hc
    push_neg at hc
    exact Nat.findGreatest_is_greatest (P := Nat.Prime) (by omega) hc hn2
  have hg := yp_next hYP hpP (by omega)
  exact ⟨p, hpP, by omega, hpy, by omega⟩

/-- Section 4 with Young-Potler, CONDITIONAL ON YoungPotler: every odd `N` with
`7 ≤ N ≤ 7.263·10^13` is a sum of three primes. Even Goldbach to 1000 suffices here. -/
theorem ternary_upto_YP (hYP : YoungPotler) {N : ℕ} (hN : Odd N) (h7 : 7 ≤ N)
    (hNx : N ≤ 72630000000000) : IsTernarySum N := by
  obtain ⟨p, hp, hp2, hpy, hyp⟩ := big_prime_below hYP (y := N - 4) (by omega) (by omega)
  exact Richstein2001.ternary_of_prime_near (M := 1000) evenGoldbachUpTo_1000 hN hp hp2
    (by omega) (by omega)

/-- Section 4 with Young-Potler and the 4·10^11 check, CONDITIONAL ON YoungPotler and
`EvenGoldbachUpTo (4·10^11)`: every odd `N` with `7 ≤ N ≤ 7.263·10^13 + 4·10^11 - 1000`
is a sum of three primes. -/
theorem ternary_upto_YP_S (hYP : YoungPotler) (hS : EvenGoldbachUpTo (4 * 10 ^ 11)) {N : ℕ}
    (hN : Odd N) (h7 : 7 ≤ N) (hNx : N ≤ 73029999999000) : IsTernarySum N := by
  obtain ⟨p, hp, hp2, hpy, hyp⟩ :=
    big_prime_below hYP (y := min (N - 4) 72630000000000) (by omega) (by omega)
  exact Richstein2001.ternary_of_prime_near hS hN hp hp2 (by omega) (by omega)

/-- Vacuity test of the unconditional hypotheses: `N = 7` and `N = 73029999999000 - 1` are
odd and in range, and the bound 73029999999000 equals 7.263·10^13 + 4·10^11 - 1000. -/
theorem vacuity : Odd 7 ∧ Odd (73029999999000 - 1) ∧ 7 ≤ 73029999999000 - 1 ∧
    (73029999999000 : ℕ) = 7263 * 10 ^ 10 + 4 * 10 ^ 11 - 1000 := by
  refine ⟨by decide, ⟨36514999999499, by norm_num⟩, by norm_num, by norm_num⟩

end LeanLab.Sinisalo1993.Ternary

#print axioms LeanLab.Sinisalo1993.Ternary.ternary_upto_YP
#print axioms LeanLab.Sinisalo1993.Ternary.ternary_upto_YP_S
#print axioms LeanLab.Sinisalo1993.Ternary.vacuity

/-
Supply split for DecompJ1133.large_even_lower. The sealed file is unchanged.
Ramaré 1995 Section 9 p. 704 uses finite Goldbach and prime intervals in a greedy descent.
The interval input below restricts the published Ramaré and Saouter 2003 Theorem 3 p. 13.
It uses the same constants as the existing Greedy module. It is not a quotation of 1995.
The two open inputs concern two primes and one prime separately. Neither restates six primes.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Ramare1995.Greedy

namespace LeanLab.Ramare1995.Decomp369a
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

/-- The p. 704 descent needs prime intervals only up to the starting bound.
CONDITIONAL ON finite Goldbach and the bounded prime interval input. -/
theorem bounded_greedy
    (hG : EvenGoldbachUpTo (2 * 10 ^ 10))
    (hI : ∀ y : ℕ, 2 * 10 ^ 10 - 3 < y → y ≤ 4 * 10 ^ 32 →
      ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ 28314000 * (y - p) < y) :
    ∀ N : ℕ, Even N → N ≤ 4 * 10 ^ 32 → AtMostPrimes 6 N := by
  intro N hN hle
  have hN2 : N % 2 = 0 := Nat.even_iff.mp hN
  rcases le_or_gt N (2 * 10 ^ 10) with hs | hb
  · exact (atMost2_of_even hG hN hs).mono (by norm_num)
  have P3 := AtMostPrimes.prime Nat.prime_three
  obtain ⟨p1, hp1, hp1le, h1⟩ := hI (N - 3) (by omega) (by omega)
  have o1 := Greedy.odd_of_big hp1 (by omega) h1 hp1le
  set x1 := N - 3 - p1 with hx1
  rcases le_or_gt x1 (2 * 10 ^ 10) with s1 | b1
  · have hx := Greedy.two_le_of_even hG (by omega) s1
    have := (P3.add (AtMostPrimes.prime hp1)).add hx
    rw [show 3 + p1 + x1 = N by omega] at this
    exact this.mono (by norm_num)
  obtain ⟨p2, hp2, hp2le, h2⟩ := hI x1 (by omega) (by omega)
  have o2 := Greedy.odd_of_big hp2 (by omega) h2 hp2le
  set x2 := x1 - p2 with hx2
  rcases le_or_gt x2 (2 * 10 ^ 10 - 3) with s2 | b2
  · have hx := Greedy.two_le_of_even hG (E := x2 + 3) (by omega) (by omega)
    have := ((AtMostPrimes.prime hp1).add (AtMostPrimes.prime hp2)).add hx
    rw [show p1 + p2 + (x2 + 3) = N by omega] at this
    exact this.mono (by norm_num)
  obtain ⟨p3, hp3, hp3le, h3⟩ := hI x2 b2 (by omega)
  have o3 := Greedy.odd_of_big hp3 (by omega) h3 hp3le
  set x3 := x2 - p3 with hx3
  have s3 : x3 ≤ 2 * 10 ^ 10 := by omega
  have hx := Greedy.two_le_of_even hG (E := x3) (by omega) s3
  have := ((((P3.add (AtMostPrimes.prime hp1)).add (AtMostPrimes.prime hp2)).add
    (AtMostPrimes.prime hp3)).add hx)
  rw [show 3 + p1 + p2 + p3 + x3 = N by omega] at this
  exact this

/-- LEAF. Ramaré 1995 p. 704, the finite Goldbach input cited as reference 2.
Every even integer from 4 through 2 times 10^10 is a sum of two primes.
This is a finite input to the descent, not the six prime conclusion. -/
theorem finite_goldbach : EvenGoldbachUpTo (2 * 10 ^ 10) := by
  sorry

/-- LEAF. Bounded interval input for the greedy argument on Ramaré 1995 p. 704.
Ramaré and Saouter 2003 Theorem 3 p. 13 supplies this restricted natural number form.
The display is x times 1 minus 1 divided by 28314000, strictly below a prime at most x.
Only 2 times 10^10 minus 3 less than y at most 4 times 10^32 is needed here. -/
theorem bounded_prime_interval (y : ℕ) (hy : 2 * 10 ^ 10 - 3 < y)
    (hu : y ≤ 4 * 10 ^ 32) :
    ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ 28314000 * (y - p) < y := by
  sorry

/-- Supply assembly of the exact lower leaf statement.
CONDITIONAL ON finite_goldbach and bounded_prime_interval. No sorry of its own. -/
theorem large_even_lower (n : ℕ) (hn : Even n) (h1 : 10 ^ 30 < n) (h2 : n ≤ 4 * 10 ^ 32) :
    AtMostPrimes 6 n :=
  bounded_greedy finite_goldbach bounded_prime_interval n hn h2

end LeanLab.Ramare1995.Decomp369a

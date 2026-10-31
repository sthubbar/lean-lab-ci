/-
Ramaré 1995, P0008, Section 9, page 704: the greedy argument for even N below 6 n₀, and the
assembly of Theorem 1 and the Corollary from the paper's inputs.
The paper's short interval input [9], "Short effective intervals containing primes", was
published as Ramaré and Saouter 2003, P0099; the lab uses its Theorem 3 in the natural number
form `LeanLab.Tao2012.RSShortIntervals`, Δ = 28 314 000 for y > 10 726 905 041. The constants
of the 1995 preprint may differ; the argument needs only some Δ with Δ³ · 2 · 10^10 above 4 · 10^32.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0803Z-2223. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Ramare1995.Statements
import LeanLab.Ramare1995.HypB
import LeanLab.Tao2012.SmallRange

namespace LeanLab.Ramare1995.Greedy
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

lemma odd_of_big {y p : ℕ} (hp : p.Prime) (hy : 10726905041 < y) (h : 28314000 * (y - p) < y)
    (hpy : p ≤ y) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | h2
  · subst h2; omega
  · exact h2

lemma two_le_of_even {E : ℕ} (hG : EvenGoldbachUpTo (2 * 10 ^ 10)) (h : E % 2 = 0)
    (hE : E ≤ 2 * 10 ^ 10) : AtMostPrimes 2 E :=
  atMost2_of_even hG (Nat.even_iff.mpr h) hE

/-- **The greedy argument, page 704.** With Ramaré-Saouter short intervals and even Goldbach up
to `2 · 10^10`, every even `N ≤ 4 · 10^32` is a sum of at most 6 primes: subtract 3, then at
most three primes from short intervals, and finish with even Goldbach. The paper says "at most
four times"; three suffice for this Δ. -/
theorem small_even_of (hRS : LeanLab.Tao2012.RSShortIntervals)
    (hG : EvenGoldbachUpTo (2 * 10 ^ 10)) :
    ∀ N : ℕ, Even N → N ≤ 4 * 10 ^ 32 → AtMostPrimes 6 N := by
  intro N hN hle
  have hN2 : N % 2 = 0 := Nat.even_iff.mp hN
  rcases le_or_gt N (2 * 10 ^ 10) with hs | hb
  · exact (atMost2_of_even hG hN hs).mono (by norm_num)
  have P3 := AtMostPrimes.prime Nat.prime_three
  -- step 1 on x0 = N - 3
  obtain ⟨p1, hp1, hp1le, h1⟩ := hRS (N - 3) (by omega)
  simp only [LeanLab.Tao2012.Δ] at h1
  have o1 := odd_of_big hp1 (by omega) h1 hp1le
  set x1 := N - 3 - p1 with hx1
  rcases le_or_gt x1 (2 * 10 ^ 10) with s1 | b1
  · have hx := two_le_of_even hG (by omega) s1
    have := (P3.add (AtMostPrimes.prime hp1)).add hx
    rw [show 3 + p1 + x1 = N by omega] at this
    exact this.mono (by norm_num)
  -- step 2 on x1, even
  obtain ⟨p2, hp2, hp2le, h2⟩ := hRS x1 (by omega)
  simp only [LeanLab.Tao2012.Δ] at h2
  have o2 := odd_of_big hp2 (by omega) h2 hp2le
  set x2 := x1 - p2 with hx2
  rcases le_or_gt x2 (2 * 10 ^ 10 - 3) with s2 | b2
  · have hx := two_le_of_even hG (E := x2 + 3) (by omega) (by omega)
    have := ((AtMostPrimes.prime hp1).add (AtMostPrimes.prime hp2)).add hx
    rw [show p1 + p2 + (x2 + 3) = N by omega] at this
    exact this.mono (by norm_num)
  -- step 3 on x2, odd
  obtain ⟨p3, hp3, hp3le, h3⟩ := hRS x2 (by omega)
  simp only [LeanLab.Tao2012.Δ] at h3
  have o3 := odd_of_big hp3 (by omega) h3 hp3le
  set x3 := x2 - p3 with hx3
  have s3 : x3 ≤ 2 * 10 ^ 10 := by omega
  have hx := two_le_of_even hG (E := x3) (by omega) s3
  have := ((((P3.add (AtMostPrimes.prime hp1)).add (AtMostPrimes.prime hp2)).add
    (AtMostPrimes.prime hp3)).add hx)
  rw [show 3 + p1 + p2 + p3 + x3 = N by omega] at this
  exact this

/-- **Theorem 1 of Ramaré 1995 from the paper's inputs.** Theorem 2, Theorem 9.1 of
Deshouillers, even Goldbach to `2 · 10^10` of Granville, van de Lune and te Riele, and the short
interval theorem of Ramaré and Saouter imply that every even integer is a sum of at most 6
primes. Hypothesis (b) of Theorem 9.1 is PROVED in HypB.lean. -/
theorem theorem1_of_inputs (h2 : Theorem2) (h91 : Theorem91)
    (hG : EvenGoldbachUpTo (2 * 10 ^ 10)) (hRS : LeanLab.Tao2012.RSShortIntervals) :
    ∀ N : ℕ, Even N → AtMostPrimes 6 N := by
  intro N hN
  rcases le_or_gt N (4 * 10 ^ 32) with h | h
  · exact small_even_of hRS hG N hN h
  · exact LeanLab.Ramare1995.HypB.large_even_of' h2 h91 hG N hN (by simp only [n₀]; omega)

/-- **The Corollary**, every integer larger than 1 is a sum of at most 7 primes, from the same
four inputs. -/
theorem corollary_of_inputs (h2 : Theorem2) (h91 : Theorem91)
    (hG : EvenGoldbachUpTo (2 * 10 ^ 10)) (hRS : LeanLab.Tao2012.RSShortIntervals) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 7 n :=
  LeanLab.Ramare1995.corollary_of (theorem1_of_inputs h2 h91 hG hRS)

end LeanLab.Ramare1995.Greedy

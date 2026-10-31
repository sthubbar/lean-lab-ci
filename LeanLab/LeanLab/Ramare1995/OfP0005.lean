/-
P0008 Ramaré 1995, "On Šnirel'man's constant": the even Goldbach input to `2 · 10^10`,
Granville, van de Lune and te Riele 1989, discharged from P0005, Oliveira e Silva, Herzog,
Pardi 2014, taken as the hypothesis `EvenGoldbachUpTo (4 * 10 ^ 18)`, the same statement as
the cited `LeanLab.Verifications.oesilva_even`, verified faithful to the paper in unit U-7300.

Both ranges use the one lab definition `EvenGoldbachUpTo N`: every even `n` with `4 ≤ n ≤ N`
is `p + q` with `p, q` prime, the prime 2 allowed. No bridge between definitions is needed;
only `2 * 10 ^ 10 ≤ 4 * 10 ^ 18`.

`theorem1_of_P0005`: every even integer is a sum of at most 6 primes, and `corollary_of_P0005`:
every integer above 1 is a sum of at most 7 primes, both CONDITIONAL ON Ramaré's Theorem 2,
Ramaré-Saouter 2003 Theorem 3 in the form `RSShortIntervals`, and P0005.

AI-written Lean code, Claude, 2026-10-21, run MANUAL-N3, unit U-7304. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Ramare1995.Theorem1

namespace LeanLab.Ramare1995.OfP0005
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

/-- P0005 gives the paper's even range `2 · 10^10`. -/
theorem even2e10_of_P0005 (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    EvenGoldbachUpTo (2 * 10 ^ 10) :=
  fun n he h4 hn => hP0005 n he h4 (hn.trans (by norm_num))

/-- **Theorem 1, CONDITIONAL ON P0005**: every even integer is a sum of at most 6 primes,
from Theorem 2, Ramaré-Saouter Theorem 3 and P0005. -/
theorem theorem1_of_P0005 (h2 : Theorem2) (hRS : LeanLab.Tao2012.RSShortIntervals)
    (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) : ∀ N : ℕ, Even N → AtMostPrimes 6 N :=
  LeanLab.Ramare1995.Theorem1.theorem1_of h2 (even2e10_of_P0005 hP0005) hRS

/-- **Corollary, CONDITIONAL ON P0005**: every integer above 1 is a sum of at most 7 primes,
same inputs. -/
theorem corollary_of_P0005 (h2 : Theorem2) (hRS : LeanLab.Tao2012.RSShortIntervals)
    (hP0005 : EvenGoldbachUpTo (4 * 10 ^ 18)) : ∀ n : ℕ, 1 < n → AtMostPrimes 7 n :=
  LeanLab.Ramare1995.Theorem1.corollary_of h2 (even2e10_of_P0005 hP0005) hRS

#print axioms even2e10_of_P0005
#print axioms theorem1_of_P0005
#print axioms corollary_of_P0005

end LeanLab.Ramare1995.OfP0005

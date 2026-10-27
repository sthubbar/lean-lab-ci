/-
Ramaré 1995, P0008: Theorem 1 and the Corollary with Theorem 9.1 now PROVED.
Remaining cited inputs: Theorem 2 of the paper, the analytic heart; even Goldbach up to
2 · 10^10, Granville, van de Lune and te Riele 1989, a computation; and Ramaré-Saouter 2003
Theorem 3, short intervals containing primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0803Z-2223. Checked only by the Lean kernel.
-/
import LeanLab.Ramare1995.Greedy
import LeanLab.Ramare1995.Theorem91

namespace LeanLab.Ramare1995.Theorem1
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

/-- **Theorem 1**: every even integer is a sum of at most 6 primes, from Theorem 2, even
Goldbach to `2 · 10^10` and Ramaré-Saouter Theorem 3. -/
theorem theorem1_of (h2 : Theorem2) (hG : EvenGoldbachUpTo (2 * 10 ^ 10))
    (hRS : LeanLab.Tao2012.RSShortIntervals) : ∀ N : ℕ, Even N → AtMostPrimes 6 N :=
  LeanLab.Ramare1995.Greedy.theorem1_of_inputs h2 LeanLab.Ramare1995.Theorem91.theorem91 hG hRS

/-- **Corollary**: every integer larger than 1 is a sum of at most 7 primes, same inputs. -/
theorem corollary_of (h2 : Theorem2) (hG : EvenGoldbachUpTo (2 * 10 ^ 10))
    (hRS : LeanLab.Tao2012.RSShortIntervals) : ∀ n : ℕ, 1 < n → AtMostPrimes 7 n :=
  LeanLab.Ramare1995.corollary_of (theorem1_of h2 hG hRS)

end LeanLab.Ramare1995.Theorem1

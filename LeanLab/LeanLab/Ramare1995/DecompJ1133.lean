import Mathlib
import LeanLab.SchnirelmannConstant.Defs
import LeanLab.Ramare1995.Statements

open Finset
open scoped Classical

namespace LeanLab.Ramare1995
open LeanLab.SchnirelmannConstant

/-- LEAF: The intermediate range. -/
theorem large_even_lower (n : ℕ) (hn : Even n) (h1 : 10 ^ 30 < n) (h2 : n ≤ 4 * 10 ^ 32) :
    AtMostPrimes 6 n := sorry

/-- LEAF: The upper range. -/
theorem large_even_upper (n : ℕ) (hn : Even n) (h : 4 * 10 ^ 32 < n) :
    AtMostPrimes 6 n := sorry

/-- The assembled target theorem. -/
theorem large_even_assembly : ∀ n : ℕ, Even n → 10 ^ 30 < n → AtMostPrimes 6 n := by
  intro n hn h
  rcases Nat.lt_or_ge (4 * 10 ^ 32) n with h1 | h2
  · exact large_even_upper n hn h1
  · exact large_even_lower n hn h h2

end LeanLab.Ramare1995

/-
Split of the two DecompJ1133 leaves, CLOUD S106 burst-20261122. The original file is unchanged.
Ramaré 1995, P0008, Section 9 p. 704. The lower range is the greedy descent of Decomp369a,
CONDITIONAL ON its two leaves finite_goldbach and bounded_prime_interval. The upper range is
Theorem 9.1 with hypotheses b and c proved, CONDITIONAL ON the single leaf theorem2_leaf of
S106SplitDecomp369b, Ramaré's Theorem 2 p. 646. No new sorry in this file.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Ramare1995.Decomp369a
import LeanLab.Ramare1995.Decomp369b
import LeanLab.Ramare1995.S106SplitDecomp369b

namespace LeanLab.Ramare1995.S106SplitDecompJ1133
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

/-- Assembly of the exact statement of DecompJ1133.large_even_lower, Ramaré 1995 p. 704.
CONDITIONAL ON Decomp369a.finite_goldbach and Decomp369a.bounded_prime_interval. -/
theorem large_even_lower (n : ℕ) (hn : Even n) (h1 : 10 ^ 30 < n) (h2 : n ≤ 4 * 10 ^ 32) :
    AtMostPrimes 6 n :=
  Decomp369a.large_even_lower n hn h1 h2

/-- Assembly of the exact statement of DecompJ1133.large_even_upper, Ramaré 1995 pp. 703
to 704. CONDITIONAL ON S106SplitDecomp369b.theorem2_leaf alone. -/
theorem large_even_upper (n : ℕ) (hn : Even n) (h : 4 * 10 ^ 32 < n) :
    AtMostPrimes 6 n :=
  Decomp369b.large_even_of_count S106SplitDecomp369b.count_lower n hn
    (by simp only [n₀]; omega)

/-- The assembled target of DecompJ1133.large_even_assembly from the two split assemblies. -/
theorem large_even_assembly : ∀ n : ℕ, Even n → 10 ^ 30 < n → AtMostPrimes 6 n := by
  intro n hn h
  rcases Nat.lt_or_ge (4 * 10 ^ 32) n with h1 | h2
  · exact large_even_upper n hn h1
  · exact large_even_lower n hn h h2

end LeanLab.Ramare1995.S106SplitDecompJ1133

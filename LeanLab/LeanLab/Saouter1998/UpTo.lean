/-
Ternary Goldbach to 10000006444119, kernel checked, no cited input: Saouter1998/Ladder.lean applied to the
lab's evenGoldbachUpTo_1e8. Unit U-0360, run 20261017T2003Z-30240. AI-written Lean code, Claude,
2026-10-17. Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import LeanLab.Saouter1998.Ladder
import LeanLab.Verifications.Top50.BitUpTo1e8

namespace LeanLab.Saouter1998

/-- Every odd n with 7 ≤ n ≤ 10000006444119 is a sum of three primes, kernel checked, no cited input. -/
theorem ternaryGoldbachUpTo_ladder : TernaryGoldbachUpTo 10000006444119 :=
  ternary_of_even LeanLab.Verifications.Top50.Bits.evenGoldbachUpTo_1e8

/-- Every odd n with 7 ≤ n ≤ 10^13 is a sum of three primes, kernel checked, no cited input. -/
theorem ternaryGoldbachUpTo_1e13 : TernaryGoldbachUpTo (10 ^ 13) :=
  fun n ho h7 hn => ternaryGoldbachUpTo_ladder n ho h7 (hn.trans (by norm_num))

/-- The same range as a single explicit statement, every prime named. -/
theorem ternary_1e13_explicit : ∀ n : ℕ, Odd n → 7 ≤ n → n ≤ 10 ^ 13 →
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n :=
  ternaryGoldbachUpTo_1e13

end LeanLab.Saouter1998

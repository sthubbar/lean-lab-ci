/-
Ternary Goldbach to 100000689365487, kernel checked, no cited input: Saouter1998/B9/Ladder.lean,
a ladder of 100000 Lucas-certified primes with gaps below 10^9, applied to the lab's own
evenGoldbachUpTo_1e9. Unit U-0361, run 20261018T0103Z-27139. AI-written Lean code, Claude,
2026-10-18. Far below Saouter's 10^20 and Helfgott-Platt's 8.875e30; the point is that nothing
here is cited. Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import LeanLab.Saouter1998.B9.Ladder
import LeanLab.Verifications.Top50.BitUpTo1e9

namespace LeanLab.Saouter1998.B9

/-- Every odd n with 7 ≤ n ≤ 100000689365487 is a sum of three primes, kernel checked. -/
theorem ternaryGoldbachUpTo_ladder9 : TernaryGoldbachUpTo 100000689365487 :=
  ternary_of_even (by simpa using LeanLab.Verifications.Top50.Bits.evenGoldbachUpTo_1e9)

/-- Every odd n with 7 ≤ n ≤ 10^14 is a sum of three primes, kernel checked, no cited input. -/
theorem ternaryGoldbachUpTo_1e14 : TernaryGoldbachUpTo (10 ^ 14) :=
  fun n ho h7 hn => ternaryGoldbachUpTo_ladder9 n ho h7 (hn.trans (by norm_num))

/-- The same range as a single explicit statement, every prime named. -/
theorem ternary_1e14_explicit : ∀ n : ℕ, Odd n → 7 ≤ n → n ≤ 10 ^ 14 →
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n :=
  ternaryGoldbachUpTo_1e14

end LeanLab.Saouter1998.B9

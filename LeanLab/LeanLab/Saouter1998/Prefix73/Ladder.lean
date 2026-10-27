/-
A 1000-rung prefix of the algorithm on Saouter 1998, page 864.
The range theorem is CONDITIONAL ON even Goldbach through 400000000000.
AI wrote this Lean code for CODEX task73. Binary Goldbach is open.
-/
import LeanLab.Saouter1998.PrefixSound
import LeanLab.Saouter1998.Prefix73.Block1
import LeanLab.Saouter1998.Prefix73.Block2
import LeanLab.Saouter1998.Prefix73.Block3
import LeanLab.Saouter1998.Prefix73.Block4

namespace LeanLab.Saouter1998.Prefix73

open LeanLab.Saouter1998.PrefixCore

/-- Block 1 extends the range, conditional on the even input. -/
theorem s1 (hB : EvenGoldbachUpTo 400000000000) :
    TernaryGoldbachUpTo (99474726715393 + 400000000000) ∧ Nat.Prime 99474726715393 ∧ 3 ≤ 99474726715393 :=
  extend hB (B9.base hB) Nat.prime_three le_rfl c1 k1

/-- Block 2 extends the range, conditional on the even input. -/
theorem s2 (hB : EvenGoldbachUpTo 400000000000) :
    TernaryGoldbachUpTo (199332003315713 + 400000000000) ∧ Nat.Prime 199332003315713 ∧ 3 ≤ 199332003315713 :=
  extend hB (s1 hB).1 (s1 hB).2.1 (s1 hB).2.2 c2 k2

/-- Block 3 extends the range, conditional on the even input. -/
theorem s3 (hB : EvenGoldbachUpTo 400000000000) :
    TernaryGoldbachUpTo (299203959980033 + 400000000000) ∧ Nat.Prime 299203959980033 ∧ 3 ≤ 299203959980033 :=
  extend hB (s2 hB).1 (s2 hB).2.1 (s2 hB).2.2 c3 k3

/-- Block 4 extends the range, conditional on the even input. -/
theorem s4 (hB : EvenGoldbachUpTo 400000000000) :
    TernaryGoldbachUpTo (399059307200513 + 400000000000) ∧ Nat.Prime 399059307200513 ∧ 3 ≤ 399059307200513 :=
  extend hB (s3 hB).1 (s3 hB).2.1 (s3 hB).2.2 c4 k4

/-- The prefix reaches this ternary range, conditional on the even input. -/
theorem ternary_prefix (hB : EvenGoldbachUpTo 400000000000) :
    TernaryGoldbachUpTo 399459307200513 := (s4 hB).1

/-- The top rung of this prefix is prime without an even Goldbach hypothesis. -/
theorem top_prime : Nat.Prime 399059307200513 := by
  have h := prime_of_test (R := 95143153) (k := 2868464) (by decide +kernel)
  exact h

end LeanLab.Saouter1998.Prefix73

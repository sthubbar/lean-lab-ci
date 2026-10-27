/-
P0042 GvLtR 1989, Section 2 arithmetic, checked. Run 20261018T1103Z-12430, unit U-0942.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base

namespace LeanLab.GvLtR1989.Paper

open LeanLab.Verifications.Top50

/-- IMAX1 = 182 for the even numbers below 10^8: PR(182), the 182nd odd prime, is 1093, the
Stein-Stein bound; and PR(20) = 73. -/
theorem PR_182 : P10k[182]? = some 1093 ∧ P10k[20]? = some 73 ∧ P10k[400]? = some 2749 := by
  decide +kernel

/-- 10000 even numbers at 3 clock cycles of 20 ns: 0.6 ms; 20 steps over 5·10^9 numbers in
blocks of 10^4: 6000 s. -/
theorem where_time : 10000 * 3 * 20 = (600000 : ℕ) ∧
    (20 : ℚ) * (6 / 10000) * (5 * 10 ^ 9) / 10 ^ 4 = 6000 := by norm_num

end LeanLab.GvLtR1989.Paper

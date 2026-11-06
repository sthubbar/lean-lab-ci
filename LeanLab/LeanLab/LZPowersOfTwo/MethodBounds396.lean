/-
P0079 page 6, a negative coefficient check for the available sieve route.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Statements

open Real
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 6, the calibration C equals twice B times one plus A.
The coefficient 16 is already too large to recover the printed C by this
calibration. PNTPort MontgomeryTwin gives the still larger asymptotic
Bombieri Davenport coefficient 16 divided by the twin-prime constant.
This theorem is the exact rational coefficient comparison alone. -/
theorem montgomery_constant_gap396 :
    bigC < 2 * (16 : ℝ) * (1 + 0.2792521041) := by
  norm_num [bigC]

end LeanLab.LZPowersOfTwo

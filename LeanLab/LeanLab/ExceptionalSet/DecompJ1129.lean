import Mathlib
import LeanLab.ExceptionalSet.Statements
import LeanLab.ExceptionalSet.BhowmikGrimmelt2026

namespace LeanLab.ExceptionalSet.BG2026_Decomp

open LeanLab.ExceptionalSet

/-- LEAF 1: The fraction 7/10 is strictly less than 0.72. -/
lemma leaf_fraction_lt : (7 / 10 : ℝ) < 0.72 := by norm_num

/-- LEAF 2: Any sequence with a power bound of 7/10 is eventually below 0.72. -/
lemma leaf_bound_implies : PowerBound (7 / 10) → EventuallyBelow 0.72 :=
  eventuallyBelow_of_powerBound leaf_fraction_lt

/-- LEAF 3: The exceptional set has a power bound of 7/10 by the recent breakthrough. -/
lemma leaf_zhao_applies : PowerBound (7 / 10) := zhao

theorem prop64_E : EventuallyBelow 0.72 :=
  leaf_bound_implies leaf_zhao_applies

end LeanLab.ExceptionalSet.BG2026_Decomp

import LeanLab.HelfgottMajor.SPLIT_very_low_zero_count
import LeanLab.HelfgottMajor.Decomp388a

/-!
An elementary sibling supply from the remaining sorry inventory.
Source P0014 page 39, the very low count at height one.
The original sealed split file stays unchanged for reviewer integration.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Supply457
open Decomp389a Decomp388a

/-- Exactly the very low count comparison with the plane indexed count at one.
Source P0014 page 39, the paragraph after display 4.30.
-/
theorem very_low_count_le_zero_count_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ, veryLowCountTerm χ T ρ) ≤ zeroCount χ 1 := by
  have hh := Decomp389a.very_low_count_le_strip_count q χ T hT
  simpa only [zeroCount, zeroWeight, ← tsum_subtype] using! hh

end LeanLab.HelfgottMajor.Supply457

#print axioms LeanLab.HelfgottMajor.Supply457.very_low_count_le_zero_count_one

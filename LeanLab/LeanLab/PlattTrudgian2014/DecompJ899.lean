/-
AI wrote this Lean code. Binary Goldbach is open.
Decomposition of PintzProductActual125 from PlattTrudgian2014 page 2.
-/
import LeanLab.PlattTrudgian2014.C2Actual125

namespace LeanLab.PlattTrudgian2014

/-- LEAF. P0024 page 2 lower bound for C2 * C0. -/
theorem pt_c2_c0_lower_bound899 : 1.2783521041 < actualC2_125 * paperC0 := by sorry

/-- LEAF. P0024 page 2 upper bound for C2 * C0. -/
theorem pt_c2_c0_upper_bound899 : actualC2_125 * paperC0 < 1.2784421041 := by sorry

/-- Assembly of PintzProductActual125. -/
theorem PintzProductActual125_decomposed899 : PintzProductActual125 := by
  unfold PintzProductActual125
  exact ⟨pt_c2_c0_lower_bound899, pt_c2_c0_upper_bound899⟩

end LeanLab.PlattTrudgian2014

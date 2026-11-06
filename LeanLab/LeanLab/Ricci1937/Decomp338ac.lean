import LeanLab.Ricci1937.Decomp338n

/-!
Ricci 1937, complete first three mixed pairs.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

/-- The full Z five and seven half of first memoir Theorem D on page 75.
The clean lower supplier is combined with the existing clean upper count. -/
theorem decomp338_Z_5_7 : TheoremDZ 5 7 := by
  exact decompJ365_Z_of_lower decomp338_Z_lower_5_7

/-- The complete five and seven pair of first memoir Theorem D on page 75. -/
theorem decomp338_D_5_7 : TheoremD 5 7 := by
  exact ⟨decomp338_Z_5_7, decomp338_W_5_7⟩

/-- The full Z four and nine half of first memoir Theorem D on page 75.
The clean lower supplier is combined with the existing clean upper count. -/
theorem decomp338_Z_4_9 : TheoremDZ 4 9 := by
  exact decompJ365_Z_of_lower decomp338_Z_lower_4_9

/-- The complete four and nine pair of first memoir Theorem D on page 75. -/
theorem decomp338_D_4_9 : TheoremD 4 9 := by
  exact ⟨decomp338_Z_4_9, decomp338_W_4_9⟩

/-- The full Z three and fifteen half of first memoir Theorem D on page 75.
The clean lower supplier is combined with the existing clean upper count. -/
theorem decomp338_Z_3_15 : TheoremDZ 3 15 := by
  exact decompJ365_Z_of_lower decomp338_Z_lower_3_15

/-- The complete three and fifteen pair of first memoir Theorem D on page 75. -/
theorem decomp338_D_3_15 : TheoremD 3 15 := by
  exact ⟨decomp338_Z_3_15, decomp338_W_3_15⟩

end LeanLab.Ricci1937

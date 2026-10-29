import LeanLab.Ricci1937.TheoremsCD

/-!
Ricci 1937, Theorem D, pages 88 and 89.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real

noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 89, the Z half of Theorem D for (6, 6). -/
theorem decompJ365_Z_6_6 : TheoremDZ 6 6 := by sorry

/-- LEAF. Page 89, the W half of Theorem D for (6, 6). -/
theorem decompJ365_W_6_6 : TheoremDW 6 6 := by sorry

/-- LEAF. Page 89, the Z half of Theorem D for (5, 7). -/
theorem decompJ365_Z_5_7 : TheoremDZ 5 7 := by sorry

/-- LEAF. Page 89, the W half of Theorem D for (5, 7). -/
theorem decompJ365_W_5_7 : TheoremDW 5 7 := by sorry

/-- LEAF. Page 89, the Z half of Theorem D for (4, 9). -/
theorem decompJ365_Z_4_9 : TheoremDZ 4 9 := by sorry

/-- LEAF. Page 89, the W half of Theorem D for (4, 9). -/
theorem decompJ365_W_4_9 : TheoremDW 4 9 := by sorry

/-- LEAF. Page 89, the Z half of Theorem D for (3, 15). -/
theorem decompJ365_Z_3_15 : TheoremDZ 3 15 := by sorry

/-- LEAF. Page 89, the W half of Theorem D for (3, 15). -/
theorem decompJ365_W_3_15 : TheoremDW 3 15 := by sorry

/-- LEAF. Page 90, the Z half of Theorem D for (2, 366). -/
theorem decompJ365_Z_2_366 : TheoremDZ 2 366 := by sorry

/-- LEAF. Page 90, the W half of Theorem D for (2, 366). -/
theorem decompJ365_W_2_366 : TheoremDW 2 366 := by sorry

/-- The final assembly matching exactly the cited `ricciD`. -/
theorem ricciD_decompJ365 : TheoremD 6 6 ∧ TheoremD 5 7 ∧ TheoremD 4 9 ∧ TheoremD 3 15 ∧ TheoremD 2 366 := by
  exact ⟨⟨decompJ365_Z_6_6, decompJ365_W_6_6⟩,
         ⟨decompJ365_Z_5_7, decompJ365_W_5_7⟩,
         ⟨decompJ365_Z_4_9, decompJ365_W_4_9⟩,
         ⟨decompJ365_Z_3_15, decompJ365_W_3_15⟩,
         ⟨decompJ365_Z_2_366, decompJ365_W_2_366⟩⟩

end
end LeanLab.Ricci1937

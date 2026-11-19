/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2560000 through 2569999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2560000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2560000 through 2569999. -/
def shifts : List ℕ := [6297984, 5744768, 5562752, 5323008, 5951232, 1485440, 6075008, 1622400, 4230144, 589184, 5317248, 2772992, 1191680, 2246784, 86912, 3295872, 5208320, 76800, 5840768, 5881344, 2515968, 26624, 2259840, 1537280, 1310592, 353024, 2020608, 1772672, 1203072, 910208, 3685760, 1563008, 130944, 2174592, 1476224, 850944, 2573312, 1491072, 5016704, 1557888, 863232, 2897792, 204672, 2168064, 1460480, 0, 2376192, 1120640, 993152, 2571008, 2413952, 1914240, 1835520, 128768]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6807811 + 2 * t ∧ (6807811 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6807811) (count := 10000)
    (lo := 2) (W := 6827808) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2560000

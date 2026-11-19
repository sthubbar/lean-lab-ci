/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window3

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 3. -/
def shifts3 : List ℕ := [3893376, 3406208, 3880320, 3558656, 3808128, 2543744, 3801600, 1477760, 3170816, 3654144, 2956928, 3547776, 2793344, 3676416, 3109760, 3460608, 3118976, 3191424, 2832128, 1045760, 2496768, 1257984, 1979264, 2484480, 2825216, 1720448, 3469056, 1617920, 1838208, 3196544, 3340416, 0, 2626688, 1762304, 1296384, 366720, 2437376, 945024, 1199360, 1878656, 501888, 1180928, 2265216, 3224064, 1986560, 606464, 3031680, 1336448, 2418816, 2224128, 3094016, 3255936, 1948544, 1499904, 1660160, 1923584, 1710336, 437120, 1764480, 1547264, 1306496, 937344, 688128, 2836608, 1662336]

/-- LEAF: Small prime differences for window 3, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts3, s ≤ 3921347 + 2 * t ∧ (3921347 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 3921347) (count := 100000)
    (lo := 2) (W := 4121344) shifts3 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window3

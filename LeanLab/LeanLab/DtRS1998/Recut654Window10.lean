/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window10

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 10. -/
def shifts10 : List ℕ := [5319296, 4929408, 4473600, 4204544, 4406528, 4149504, 3469056, 1477760, 3224064, 4206848, 3547776, 3170816, 3880320, 3196544, 3808128, 437120, 1257984, 1195520, 3801600, 3118976, 3460608, 1412864, 1662336, 1180928, 1617920, 1633536, 1296384, 2825216, 0, 4531328, 1838208, 2793344, 3191424, 2956928, 556416, 2222720, 845568, 1878656, 1764480, 3094016, 2418816, 2832128, 2944128, 1336448, 1547264, 2224128, 308480, 1883136, 3406208, 2265216, 1979264, 945024, 1710336, 1762304, 3558656, 3124608, 2590208, 3031680, 1154688, 2437376, 1306496, 1227264, 4047488, 2543744, 2005376, 688128, 3893376, 2718336, 1986560]

/-- LEAF: Small prime differences for window 10, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts10, s ≤ 5321347 + 2 * t ∧ (5321347 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 5321347) (count := 100000)
    (lo := 2) (W := 5521344) shifts10 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window10

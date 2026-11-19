/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window16

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 16. -/
def shifts16 : List ℕ := [6080768, 5863680, 5319296, 4149504, 5777024, 4929408, 3469056, 4531328, 4473600, 1986560, 1257984, 3118976, 3808128, 1762304, 1477760, 2418816, 945024, 3170816, 4206848, 1662336, 2543744, 3880320, 1617920, 3676416, 2944128, 1547264, 688128, 2956928, 3224064, 2222720, 1883136, 2759936, 2496768, 2825216, 760704, 4204544, 3801600, 2832128, 1195520, 1710336, 1180928, 845568, 0, 1923584, 556416, 1045760, 937344, 2005376, 3893376, 3109760, 1720448, 2224128, 2626688, 2484480, 3094016, 1227264, 1199360, 1412864, 3031680, 3340416, 734976, 2590208, 2793344, 2564096, 2049024, 1878656, 501888, 3124608, 1764480, 4047488, 2437376, 3460608, 3558656, 3547776]

/-- LEAF: Small prime differences for window 16, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts16, s ≤ 6521347 + 2 * t ∧ (6521347 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6521347) (count := 100000)
    (lo := 2) (W := 6721344) shifts16 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window16

/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window20

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 20. -/
def shifts20 : List ℕ := [7196288, 6956544, 6650240, 6950784, 6841856, 5863680, 3676416, 7378304, 2796288, 2754176, 3880320, 4047488, 5777024, 3460608, 4473600, 3109760, 2265216, 1412864, 2759936, 1883136, 4406528, 3031680, 2944128, 1195520, 3654144, 3094016, 6080768, 556416, 1617920, 501888, 2825216, 1227264, 1923584, 845568, 734976, 4531328, 2484480, 2793344, 1547264, 1764480, 1660160, 2496768, 3147776, 1633536, 2832128, 1838208, 1316864, 760704, 1210496, 1710336, 3224064, 1306496, 4204544, 1662336, 2626688, 2418816, 1154688, 0, 2005376, 1477760, 2224128, 2590208, 1257984, 1878656, 1948544, 937344, 3801600, 2956928, 2437376, 1762304, 7514880]

/-- LEAF: Small prime differences for window 20, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts20, s ≤ 7321347 + 2 * t ∧ (7321347 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7321347) (count := 100000)
    (lo := 2) (W := 7521344) shifts20 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window20

/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window22

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 22. -/
def shifts22 : List ℕ := [7708544, 7584768, 7514880, 6841856, 7474304, 6956544, 7196288, 3893376, 6650240, 5863680, 2944128, 6080768, 6950784, 3109760, 1883136, 2754176, 7378304, 4473600, 4929408, 4047488, 1710336, 2825216, 3880320, 1195520, 3224064, 3558656, 3676416, 1986560, 2496768, 1720448, 1296384, 2543744, 556416, 5777024, 3031680, 2590208, 2836608, 1180928, 3801600, 2005376, 945024, 2222720, 4009728, 1547264, 3469056, 3118976, 1764480, 2626688, 1412864, 3547776, 3808128, 2956928, 1878656, 1257984, 3255936, 3196544, 688128, 3094016, 0, 1979264, 3654144, 2759936, 2796288, 1477760, 1210496, 3460608, 3147776, 3170816, 2832128, 3191424, 1499904, 1246848, 2564096, 1154688, 3340416]

/-- LEAF: Small prime differences for window 22, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts22, s ≤ 7721347 + 2 * t ∧ (7721347 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7721347) (count := 100000)
    (lo := 2) (W := 7921344) shifts22 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window22

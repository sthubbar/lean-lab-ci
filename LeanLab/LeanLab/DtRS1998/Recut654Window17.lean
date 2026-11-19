/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window17

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 17. -/
def shifts17 : List ℕ := [6650240, 5863680, 6080768, 3191424, 5319296, 4929408, 3340416, 5777024, 3469056, 4406528, 1499904, 1412864, 3801600, 2825216, 4009728, 1195520, 3893376, 4531328, 1227264, 3118976, 4473600, 606464, 1246848, 3109760, 937344, 4204544, 2418816, 2832128, 1154688, 1986560, 1257984, 3170816, 3460608, 1477760, 2484480, 1720448, 3255936, 1979264, 760704, 1878656, 3124608, 1617920, 3676416, 2793344, 657408, 1180928, 1764480, 2222720, 0, 2564096, 945024, 1336448, 2496768, 2759936, 845568, 1948544, 2265216, 3406208, 1306496, 2718336, 2049024, 4047488, 1633536, 1923584, 1710336, 2796288, 2626688, 1199360, 501888, 2590208, 3547776, 3880320]

/-- LEAF: Small prime differences for window 17, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts17, s ≤ 6721347 + 2 * t ∧ (6721347 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6721347) (count := 100000)
    (lo := 2) (W := 6921344) shifts17 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window17

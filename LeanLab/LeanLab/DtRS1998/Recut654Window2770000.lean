/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2770000 through 2779999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2770000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2770000 through 2779999. -/
def shifts : List ℕ := [6230784, 6107008, 5364096, 6453760, 5718528, 5478784, 5996544, 4385920, 2070016, 1632000, 1466368, 1479168, 5473024, 1693056, 2928768, 2995840, 1282176, 2198656, 4603008, 2323840, 22144, 445824, 1616256, 1982848, 5900544, 2402560, 5172480, 2176384, 1670016, 746368, 140160, 1991296, 501504, 286720, 3053568, 941056, 1928448, 1713664, 3841536, 1318528, 184576, 1641216, 1065984, 232576, 1862656, 527616, 69504, 2569728, 1646848, 0, 6037120, 3451648, 2729088, 2330368, 1006720]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7383587 + 2 * t ∧ (7383587 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7383587) (count := 10000)
    (lo := 2) (W := 7403584) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2770000

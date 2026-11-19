/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2760000 through 2769999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2760000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2760000 through 2769999. -/
def shifts : List ℕ := [6453760, 6230784, 4603008, 6107008, 5478784, 2080896, 2415616, 5172480, 5996544, 1358848, 5473024, 5364096, 1112448, 4385920, 1991296, 4299264, 360448, 1479168, 2995840, 1641216, 2671744, 0, 1466368, 1928448, 941056, 140160, 527616, 2402560, 746368, 69504, 1746304, 5900544, 1276416, 2198656, 2330368, 1065984, 242688, 1240576, 3841536, 284544, 1553920, 787456, 3053568, 232576, 1616256, 22144, 2928768, 1693056, 286720, 6037120, 2729088, 2569728, 2176384, 1670016, 1086336, 470784]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7363587 + 2 * t ∧ (7363587 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7363587) (count := 10000)
    (lo := 2) (W := 7383584) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2760000

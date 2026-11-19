/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2420000 through 2429999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2420000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2420000 through 2429999. -/
def shifts : List ℕ := [6453760, 6230784, 6107008, 5364096, 5478784, 5996544, 5718528, 2070016, 1632000, 1778176, 5172480, 5473024, 2928768, 1646848, 2080896, 2402560, 4603008, 1991296, 182400, 6037120, 1641216, 2176384, 5900544, 1862656, 1112448, 1006720, 360448, 1354368, 4299264, 2995840, 2415616, 527616, 1616256, 1746304, 1019008, 1315584, 1553920, 1282176, 959616, 571264, 501504, 232576, 787456, 140160, 3451648, 2569728, 470784, 2323840, 1693056, 1358848, 184576, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6683587 + 2 * t ∧ (6683587 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6683587) (count := 10000)
    (lo := 2) (W := 6703584) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2420000

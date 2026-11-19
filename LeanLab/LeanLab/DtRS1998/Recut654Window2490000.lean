/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2490000 through 2499999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2490000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2490000 through 2499999. -/
def shifts : List ℕ := [5982976, 5429760, 5247744, 5636224, 4893312, 5008000, 5525760, 3915136, 4701696, 1520512, 2457984, 470272, 1222272, 5002240, 5760000, 847744, 1145472, 1705600, 1859584, 615552, 1161216, 1242880, 1599232, 1457664, 38016, 5566336, 2525056, 0, 1176064, 811392, 1083136, 30720, 4132224, 2200960, 1931776, 876672, 769792, 641664, 1944832, 1853056, 1610112, 56832, 2098944, 1727872, 995584, 274176, 1008384, 548224, 535936, 2980864, 2582784, 2256000, 888064, 275584]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6352803 + 2 * t ∧ (6352803 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6352803) (count := 10000)
    (lo := 2) (W := 6372800) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2490000

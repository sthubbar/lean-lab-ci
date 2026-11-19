/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2720000 through 2729999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2720000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2720000 through 2729999. -/
def shifts : List ℕ := [5922432, 5715968, 6269184, 5179520, 5294208, 4418432, 4201344, 6046208, 1091840, 5288448, 4987904, 2231040, 1133952, 1447424, 2217984, 2744192, 5811968, 2014080, 1097600, 1529088, 834432, 2544512, 5533952, 0, 901760, 822144, 1798272, 1131008, 1885440, 1508480, 2385152, 1678080, 560384, 3267072, 1162880, 2145792, 2868992, 2139264, 1593600, 1431680, 58112, 2542208, 1561728, 1991808, 4114688, 2487168, 1743872, 1294592, 5852544, 1369344, 1174272, 602880, 286208]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7099011 + 2 * t ∧ (7099011 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7099011) (count := 10000)
    (lo := 2) (W := 7119008) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2720000

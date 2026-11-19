/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2640000 through 2649999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2640000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2640000 through 2649999. -/
def shifts : List ℕ := [6269184, 6046208, 4418432, 1056000, 5179520, 5294208, 1447424, 3267072, 5715968, 4201344, 5922432, 1091840, 1806720, 4987904, 1991808, 2744192, 1678080, 5811968, 2811264, 5533952, 1561728, 1896320, 2868992, 2217984, 48000, 1508480, 5288448, 560384, 2145792, 58112, 2542208, 1133952, 5852544, 4114688, 756480, 2231040, 1294592, 0, 927872, 2385152, 1369344, 216320, 1281792, 561792, 2347392, 881408, 1162880, 286208, 2014080, 1885440, 1529088, 343040, 316928]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6939011 + 2 * t ∧ (6939011 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6939011) (count := 10000)
    (lo := 2) (W := 6959008) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2640000

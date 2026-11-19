/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are candidate displacements. They are not a second prime list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window0

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements from the least candidate used in this window. -/
def shifts0 : List ℕ := [3302272, 3242880, 3156096, 3270400, 3165312, 3078016, 3003264, 3386752, 3170944, 3217152, 3237760, 1524096, 2543104, 2839680, 2636544, 46336, 3194112, 2530816, 703744, 1664256, 1546240, 2025600, 2311552, 2878464, 3140352, 2882944, 2673024, 983680, 2269056, 2465152, 2806272, 807040, 2764672, 1593600, 734464, 0, 413056, 2871552, 1382784, 1810816, 1706496, 2842624, 1241856, 1929472, 2270464, 1227264, 1363200, 1756672, 2483712, 1459200, 781312, 2990464, 2590080, 2032896, 1884544, 2610432, 891904, 652800, 1304320, 1273600, 1679872, 548224, 1924992, 1969920, 1766784, 602752, 1342720, 1293184, 1994880, 991360, 2095360, 3452544]

/-- LEAF: Checked small prime differences for the first 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
No primality of the large candidates is assumed or asserted here. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts0, s ≤ 3367683 + 2 * t ∧ (3367683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 3367683) (count := 100000)
    (lo := 2) (W := 3567680) shifts0 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window0

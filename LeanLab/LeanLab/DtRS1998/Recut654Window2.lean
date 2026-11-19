/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 2. -/
def shifts2 : List ℕ := [3722752, 3452544, 3700480, 3604992, 3156096, 3506944, 2025600, 3594112, 1706496, 3237760, 3194112, 2990464, 3242880, 3078016, 1766784, 3515392, 3217152, 2530816, 1524096, 548224, 3165312, 1304320, 0, 3170944, 1593600, 46336, 2673024, 2543104, 1241856, 3302272, 2051712, 3270400, 2878464, 983680, 1363200, 3386752, 1245696, 1884544, 2483712, 703744, 1227264, 1679872, 1969920, 1546240, 2806272, 2311552, 354816, 807040, 1756672, 2590080, 1929472, 652800, 2882944, 2610432, 483456, 3003264, 1273600, 2764672, 1293184, 2032896, 413056, 1092096, 3847936, 2636544, 1342720, 2839680, 3140352, 2465152, 1808640, 2095360, 1664256, 1352832, 3926656]

/-- LEAF: Small prime differences for window 2, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts2, s ≤ 3767683 + 2 * t ∧ (3767683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 3767683) (count := 100000)
    (lo := 2) (W := 3967680) shifts2 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2

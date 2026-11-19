/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window9

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 9. -/
def shifts9 : List ℕ := [4975744, 4577664, 4519936, 4250880, 4195840, 3604992, 3156096, 3939712, 4253184, 3926656, 3217152, 1304320, 2025600, 4056064, 3594112, 3165312, 1706496, 3270400, 3242880, 3847936, 1227264, 891904, 1524096, 3854464, 3194112, 807040, 3515392, 4093824, 2839680, 1810816, 1273600, 1092096, 2878464, 3386752, 2871552, 1756672, 1245696, 2882944, 1459200, 1708672, 1664256, 3078016, 1342720, 2806272, 991360, 1593600, 0, 46336, 548224, 4452864, 1929472, 1884544, 483456, 3140352, 2610432, 413056, 2269056, 3003264, 2842624, 1293184, 1766784, 3170944, 2673024, 2764672, 2032896, 3237760, 2543104, 2990464, 1546240, 1969920, 2483712, 602752]

/-- LEAF: Small prime differences for window 9, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts9, s ≤ 5167683 + 2 * t ∧ (5167683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 5167683) (count := 100000)
    (lo := 2) (W := 5367680) shifts9 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window9

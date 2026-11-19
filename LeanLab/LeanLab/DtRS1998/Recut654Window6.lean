/-
AI wrote this Lean code for CODEX task654.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
These are displacements of members of the one shared row list.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window6

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for row 20 window 6. -/
def shifts6 : List ℕ := [4577664, 4519936, 4195840, 4250880, 4452864, 3594112, 3926656, 3217152, 3506944, 3156096, 2871552, 3939712, 1293184, 3242880, 1092096, 1304320, 4056064, 1664256, 3700480, 3165312, 1459200, 2764672, 1766784, 1201024, 3847936, 1524096, 3270400, 2636544, 1994880, 602752, 3194112, 2465152, 891904, 1241856, 1342720, 1227264, 2543104, 3604992, 3515392, 2673024, 3078016, 2032896, 1756672, 2051712, 983680, 2025600, 46336, 483456, 781312, 1924992, 3237760, 0, 703744, 413056, 2590080, 1546240, 1593600, 548224, 3003264, 3302272, 2610432, 1969920, 1810816, 1245696, 807040, 3854464, 2878464, 2269056, 2990464, 1708672, 2806272]

/-- LEAF: Small prime differences for window 6, with 100000 offsets.
P0037 page 210 shifted sieve, applied to page 212 row 10^200.
This asserts no primality of the large candidates. -/
theorem small_differences :
    ∀ t : ℕ, t < 100000 →
      ∃ s ∈ shifts6, s ≤ 4567683 + 2 * t ∧ (4567683 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 4567683) (count := 100000)
    (lo := 2) (W := 4767680) shifts6 (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window6

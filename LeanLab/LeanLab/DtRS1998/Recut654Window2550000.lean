/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2550000 through 2559999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2550000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2550000 through 2559999. -/
def shifts : List ℕ := [7243392, 7020416, 6268416, 6508160, 6896640, 6786176, 6153728, 5175552, 2421632, 2780928, 2256000, 5962112, 6690176, 1150080, 2066048, 6262656, 2030208, 3843200, 972032, 2966016, 2567808, 4631168, 3718400, 3192192, 2430848, 1808640, 5392640, 811776, 3516416, 3205248, 1749248, 1032320, 569856, 628736, 6826752, 3120000, 522368, 46848, 2343552, 1298432, 1190528, 3785472, 2148480, 1022208, 5088896, 2772480, 648320, 3113472, 1938560, 0]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7733219 + 2 * t ∧ (7733219 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 7733219) (count := 10000)
    (lo := 2) (W := 7753216) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2550000

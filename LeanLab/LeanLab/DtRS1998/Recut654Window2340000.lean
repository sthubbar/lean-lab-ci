/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for offsets 2340000 through 2349999.
No primality of a large row candidate is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Bitmap

namespace LeanLab.DtRS1998.Recut654Window2340000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for offsets 2340000 through 2349999. -/
def shifts : List ℕ := [6052864, 5829888, 5317632, 5706112, 4963200, 5077888, 5595648, 3985024, 4771584, 839680, 3050752, 685440, 5499648, 1775488, 2328192, 4480, 605824, 1231104, 386560, 1078272, 5072128, 875520, 2325888, 1312768, 917632, 881280, 1461760, 4202112, 1153024, 946560, 748032, 1581952, 100608, 1797760, 0, 2131072, 1269120, 1922944, 2270848, 665088, 540160, 44928, 953472, 5636224, 3898368, 1245952, 126720, 2014720, 1929472, 1680000, 1669120, 1292160, 1065472, 957952, 914688, 558720]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 6122691 + 2 * t ∧ (6122691 + 2 * t - s).Prime := by
  apply Recut654Bitmap.prime_differences_of_bitmap (A := 6122691) (count := 10000)
    (lo := 2) (W := 6142688) shifts (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  decide +kernel

end LeanLab.DtRS1998.Recut654Window2340000

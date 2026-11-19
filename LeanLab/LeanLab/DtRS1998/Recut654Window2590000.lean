/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2590000 through 2599999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2590000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7243392, 7020416, 6153728, 6896640, 6268416, 6508160, 5962112, 6262656, 3205248, 6690176, 2567808, 5392640, 2772480, 6786176, 3192192, 1534592, 6826752, 2066048, 2108160, 3359360, 1749248, 2780928, 4241280, 3843200, 2870528, 2256000, 2137088, 2859648, 5088896, 3113472, 2405888, 2436480, 3718400, 1730688, 2966016, 1855616, 3321600, 2652288, 2144000, 1875968, 2105216, 1360896, 1291136, 2030208, 1190528, 2718080, 2148480, 1808640, 5175552, 3518720, 3516416, 2459648, 1577088, 1235456, 539136, 0, 618368, 46848]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [7821303, 7824609, 7830229, 7830393, 7832391]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7813219 + 2 * t ∧ (7813219 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 7813219) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · refine ⟨539136, by decide, by decide, ?_⟩
      change Nat.Prime 7282169
      exact Recut654Exceptions.prime_of_bit 7282169 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 7824611
      exact Recut654Exceptions.prime_of_bit 7824611 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨618368, by decide, by decide, ?_⟩
      change Nat.Prime 7211863
      exact Recut654Exceptions.prime_of_bit 7211863 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨46848, by decide, by decide, ?_⟩
      change Nat.Prime 7783547
      exact Recut654Exceptions.prime_of_bit 7783547 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨539136, by decide, by decide, ?_⟩
      change Nat.Prime 7293257
      exact Recut654Exceptions.prime_of_bit 7293257 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2590000

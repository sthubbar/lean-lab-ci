/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2870000 through 2879999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2870000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [6896640, 7020416, 6153728, 5175552, 6268416, 5392640, 6786176, 7243392, 2421632, 2567808, 6262656, 5962112, 4241280, 2430848, 2780928, 6508160, 2503296, 3843200, 6690176, 6826752, 2137088, 1796352, 3461376, 2071808, 2268800, 1808640, 3192192, 2066048, 2718080, 1536000, 1749248, 2859648, 2482688, 2966016, 2535936, 1534592, 3359360, 2772480, 2144000, 4631168, 3785472, 3113472, 2652288, 2508416, 2870528, 2436480, 2256000, 3516416, 3205248, 1902080, 3718400, 2988288, 2459648, 2108160, 1855616, 507392, 0, 8375808]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8385571, 8387991, 8388747, 8392743]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8373219 + 2 * t ∧ (8373219 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8373219) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · refine ⟨507392, by decide, by decide, ?_⟩
      change Nat.Prime 7878181
      exact Recut654Exceptions.prime_of_bit 7878181 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8387993
      exact Recut654Exceptions.prime_of_bit 8387993 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨8375808, by decide, by decide, ?_⟩
      change Nat.Prime 12941
      exact Recut654Exceptions.prime_of_bit 12941 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨8375808, by decide, by decide, ?_⟩
      change Nat.Prime 16937
      exact Recut654Exceptions.prime_of_bit 16937 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2870000

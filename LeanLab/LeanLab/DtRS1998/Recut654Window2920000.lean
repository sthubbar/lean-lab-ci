/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2920000 through 2929999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2920000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [9126912, 9110272, 9123072, 7977856, 7520640, 7002880, 7242624, 7631104, 2269056, 5910016, 3237760, 4253184, 6696576, 3515392, 2882944, 7424640, 6997120, 2800512, 3847936, 7754880, 3506944, 3604992, 3722752, 2878464, 3594112, 2590080, 3926656, 4250880, 3165312, 7561216, 2842624, 4093824, 3242880, 2764672, 2806272, 4975744, 3156096, 2311552, 3854464, 2483712, 2530816, 6127104, 5365632, 4056064, 3302272, 3170944, 2543104, 3939712, 4577664, 3386752, 2839680, 0, 46336, 1706496]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9214025, 9216505, 9220903, 9222575]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9207683 + 2 * t ∧ (9207683 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9207683) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 9214027
      exact Recut654Exceptions.prime_of_bit 9214027 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨46336, by decide, by decide, ?_⟩
      change Nat.Prime 9170171
      exact Recut654Exceptions.prime_of_bit 9170171 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨46336, by decide, by decide, ?_⟩
      change Nat.Prime 9174569
      exact Recut654Exceptions.prime_of_bit 9174569 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1706496, by decide, by decide, ?_⟩
      change Nat.Prime 7516081
      exact Recut654Exceptions.prime_of_bit 7516081 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2920000

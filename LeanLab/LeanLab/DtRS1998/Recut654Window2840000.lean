/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2840000 through 2849999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2840000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7561216, 7242624, 7002880, 7520640, 6888192, 7631104, 3926656, 7754880, 3594112, 6696576, 4577664, 3939712, 7424640, 4519936, 3165312, 6997120, 4975744, 2610432, 3302272, 4253184, 2270464, 2269056, 2764672, 2878464, 3270400, 3194112, 3854464, 2800512, 5910016, 3003264, 2673024, 3237760, 3604992, 2543104, 2990464, 3156096, 2839680, 2465152, 4452864, 3170944, 3140352, 2590080, 5823360, 4056064, 2842624, 7977856, 3700480, 3217152, 4250880, 6127104, 5365632, 4195840, 4093824, 3847936, 3506944, 3242880, 3078016, 2636544, 46336, 781312, 703744, 602752, 0, 734464]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9054457, 9059233, 9060943, 9061741, 9063875, 9065509]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9047683 + 2 * t ∧ (9047683 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9047683) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨46336, by decide, by decide, ?_⟩
      change Nat.Prime 9008123
      exact Recut654Exceptions.prime_of_bit 9008123 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨781312, by decide, by decide, ?_⟩
      change Nat.Prime 8277923
      exact Recut654Exceptions.prime_of_bit 8277923 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨703744, by decide, by decide, ?_⟩
      change Nat.Prime 8357201
      exact Recut654Exceptions.prime_of_bit 8357201 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨602752, by decide, by decide, ?_⟩
      change Nat.Prime 8458991
      exact Recut654Exceptions.prime_of_bit 8458991 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 9063877
      exact Recut654Exceptions.prime_of_bit 9063877 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨734464, by decide, by decide, ?_⟩
      change Nat.Prime 8331047
      exact Recut654Exceptions.prime_of_bit 8331047 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2840000

/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2860000 through 2869999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2860000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7977856, 7424640, 7242624, 7002880, 2800512, 7631104, 3939712, 6696576, 7754880, 3926656, 2543104, 3194112, 7520640, 3302272, 4975744, 2806272, 5910016, 4452864, 3237760, 3156096, 3594112, 4250880, 3140352, 2270464, 2636544, 3386752, 6888192, 2882944, 4253184, 2465152, 5365632, 4519936, 2311552, 6127104, 3270400, 5823360, 3165312, 7561216, 3604992, 3515392, 3078016, 4577664, 3700480, 2610432, 2842624, 4195840, 4093824, 3003264, 3506944, 3217152, 2839680, 4056064, 2673024, 1241856, 602752, 1256832, 483456, 354816, 0, 703744, 781312, 991360]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9088127, 9093289, 9093797, 9094415, 9098585, 9098825, 9099145, 9101165, 9101857, 9106555]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9087683 + 2 * t ∧ (9087683 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9087683) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨1241856, by decide, by decide, ?_⟩
      change Nat.Prime 7846273
      exact Recut654Exceptions.prime_of_bit 7846273 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨602752, by decide, by decide, ?_⟩
      change Nat.Prime 8490539
      exact Recut654Exceptions.prime_of_bit 8490539 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1256832, by decide, by decide, ?_⟩
      change Nat.Prime 7836967
      exact Recut654Exceptions.prime_of_bit 7836967 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨483456, by decide, by decide, ?_⟩
      change Nat.Prime 8610961
      exact Recut654Exceptions.prime_of_bit 8610961 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨354816, by decide, by decide, ?_⟩
      change Nat.Prime 8743771
      exact Recut654Exceptions.prime_of_bit 8743771 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 9098827
      exact Recut654Exceptions.prime_of_bit 9098827 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨703744, by decide, by decide, ?_⟩
      change Nat.Prime 8395403
      exact Recut654Exceptions.prime_of_bit 8395403 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1241856, by decide, by decide, ?_⟩
      change Nat.Prime 7859311
      exact Recut654Exceptions.prime_of_bit 7859311 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨781312, by decide, by decide, ?_⟩
      change Nat.Prime 8320547
      exact Recut654Exceptions.prime_of_bit 8320547 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨991360, by decide, by decide, ?_⟩
      change Nat.Prime 8115197
      exact Recut654Exceptions.prime_of_bit 8115197 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2860000

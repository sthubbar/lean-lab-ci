/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2830000 through 2839999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2830000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7931520, 6841856, 6956544, 7196288, 7474304, 7584768, 3109760, 5863680, 6950784, 7708544, 2825216, 3469056, 4047488, 4473600, 4929408, 6650240, 3255936, 6080768, 3654144, 2832128, 2754176, 3893376, 7378304, 3031680, 2956928, 3547776, 4149504, 5777024, 2484480, 3118976, 2590208, 3124608, 4204544, 4009728, 2437376, 3808128, 4406528, 3880320, 2418816, 3224064, 3196544, 4206848, 3340416, 2222720, 3558656, 2793344, 2224128, 3676416, 4531328, 3147776, 2836608, 2796288, 2718336, 2049024, 437120, 1195520, 308480, 0, 1617920, 366720]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8983549, 8988559, 8989939, 8991469, 8991759, 8999059, 8999241]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8981347 + 2 * t ∧ (8981347 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8981347) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨437120, by decide, by decide, ?_⟩
      change Nat.Prime 8546431
      exact Recut654Exceptions.prime_of_bit 8546431 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1195520, by decide, by decide, ?_⟩
      change Nat.Prime 7793041
      exact Recut654Exceptions.prime_of_bit 7793041 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1195520, by decide, by decide, ?_⟩
      change Nat.Prime 7794421
      exact Recut654Exceptions.prime_of_bit 7794421 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨308480, by decide, by decide, ?_⟩
      change Nat.Prime 8682991
      exact Recut654Exceptions.prime_of_bit 8682991 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8991761
      exact Recut654Exceptions.prime_of_bit 8991761 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1617920, by decide, by decide, ?_⟩
      change Nat.Prime 7381141
      exact Recut654Exceptions.prime_of_bit 7381141 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨366720, by decide, by decide, ?_⟩
      change Nat.Prime 8632523
      exact Recut654Exceptions.prime_of_bit 8632523 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2830000

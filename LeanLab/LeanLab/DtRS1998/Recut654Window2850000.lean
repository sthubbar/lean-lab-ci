/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2850000 through 2859999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2850000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7931520, 7378304, 7196288, 6950784, 3170816, 7584768, 3469056, 4047488, 6956544, 7474304, 2825216, 4929408, 3109760, 2836608, 5319296, 5863680, 3893376, 4531328, 3676416, 6650240, 3880320, 4204544, 2944128, 4406528, 2626688, 2418816, 4149504, 3094016, 3801600, 7708544, 3547776, 4206848, 3224064, 6080768, 3460608, 5777024, 3558656, 4473600, 2832128, 3255936, 3196544, 2718336, 3031680, 2796288, 2793344, 2759936, 3808128, 3406208, 3340416, 2754176, 2590208, 2222720, 3654144, 2543744, 1617920, 1195520, 0, 688128]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9027349, 9029089, 9036019, 9037407, 9039939]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9021347 + 2 * t ∧ (9021347 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9021347) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · refine ⟨1617920, by decide, by decide, ?_⟩
      change Nat.Prime 7409431
      exact Recut654Exceptions.prime_of_bit 7409431 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1617920, by decide, by decide, ?_⟩
      change Nat.Prime 7411171
      exact Recut654Exceptions.prime_of_bit 7411171 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1195520, by decide, by decide, ?_⟩
      change Nat.Prime 7840501
      exact Recut654Exceptions.prime_of_bit 7840501 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 9037409
      exact Recut654Exceptions.prime_of_bit 9037409 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨688128, by decide, by decide, ?_⟩
      change Nat.Prime 8351813
      exact Recut654Exceptions.prime_of_bit 8351813 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2850000

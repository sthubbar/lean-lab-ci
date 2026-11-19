/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2950000 through 2959999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2950000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8763136, 8639616, 8643456, 6519424, 6213120, 8626816, 7037184, 2047360, 6759168, 2786944, 3572608, 2672640, 3443200, 3769728, 2106624, 4492288, 6513664, 2681856, 3767424, 7077760, 2395008, 2507008, 3121536, 3364480, 3969408, 3371008, 5339904, 3456256, 2356224, 2754304, 3610368, 7147648, 4882176, 6941184, 3031936, 2969088, 3217024, 2153088, 2594560, 2317056, 6404736, 3110656, 3023488, 2519808, 2126976, 7271424, 2818816, 2759424, 5643648, 4094208, 3712384, 2687488, 2359168, 2281216, 758400, 220288, 169344, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8789159, 8790157, 8798189, 8800439, 8800577, 8802085]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8784227 + 2 * t ∧ (8784227 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8784227) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨758400, by decide, by decide, ?_⟩
      change Nat.Prime 8030761
      exact Recut654Exceptions.prime_of_bit 8030761 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨220288, by decide, by decide, ?_⟩
      change Nat.Prime 8569871
      exact Recut654Exceptions.prime_of_bit 8569871 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨758400, by decide, by decide, ?_⟩
      change Nat.Prime 8039791
      exact Recut654Exceptions.prime_of_bit 8039791 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨169344, by decide, by decide, ?_⟩
      change Nat.Prime 8631097
      exact Recut654Exceptions.prime_of_bit 8631097 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8800579
      exact Recut654Exceptions.prime_of_bit 8800579 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨220288, by decide, by decide, ?_⟩
      change Nat.Prime 8581799
      exact Recut654Exceptions.prime_of_bit 8581799 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2950000

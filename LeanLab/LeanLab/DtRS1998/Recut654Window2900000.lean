/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2900000 through 2909999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2900000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8772096, 8755456, 8768256, 7276288, 7165824, 3571840, 6887808, 2915584, 6341760, 2528128, 7623040, 7400064, 3345664, 4098048, 3367936, 1914240, 4620928, 5555200, 5010816, 5772288, 2188288, 7069824, 1956736, 2862336, 3493120, 3739008, 6648064, 3250176, 6642304, 5468544, 2635648, 2235264, 2110336, 4222848, 2484864, 7206400, 2255616, 3097728, 3031936, 2882944, 2810496, 2723200, 3499648, 2281728, 6533376, 4165120, 2947456, 3584896, 2785536, 2451456, 2318208, 3898368, 3841024, 3239296, 3152128, 2801280, 1915648, 0, 452224, 348928, 379648, 737280]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8815319, 8816761, 8817409, 8828335, 8831489]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8812867 + 2 * t ∧ (8812867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8812867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8815321
      exact Recut654Exceptions.prime_of_bit 8815321 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨452224, by decide, by decide, ?_⟩
      change Nat.Prime 8364539
      exact Recut654Exceptions.prime_of_bit 8364539 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨348928, by decide, by decide, ?_⟩
      change Nat.Prime 8468483
      exact Recut654Exceptions.prime_of_bit 8468483 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨379648, by decide, by decide, ?_⟩
      change Nat.Prime 8448689
      exact Recut654Exceptions.prime_of_bit 8448689 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨737280, by decide, by decide, ?_⟩
      change Nat.Prime 8094211
      exact Recut654Exceptions.prime_of_bit 8094211 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2900000

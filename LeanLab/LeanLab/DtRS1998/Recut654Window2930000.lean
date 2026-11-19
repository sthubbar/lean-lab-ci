/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2930000 through 2939999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2930000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8768256, 8755456, 8772096, 7623040, 6887808, 6648064, 7165824, 7276288, 6642304, 6341760, 3571840, 7069824, 3584896, 3898368, 4620928, 3739008, 4165120, 2801280, 3841024, 7400064, 2409856, 2523648, 3701248, 2484864, 3493120, 6533376, 5555200, 2451456, 2235264, 2947456, 1915648, 3896064, 2188288, 2128896, 3345664, 3097728, 3160576, 2648448, 5468544, 2816128, 2445696, 2176000, 4222848, 2888064, 2487808, 1956736, 7206400, 4098048, 2882944, 5010816, 3499648, 2723200, 2516736, 0, 1309440, 452224, 426496]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8873069, 8884949, 8886169, 8888671]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8872867 + 2 * t ∧ (8872867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8872867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8873071
      exact Recut654Exceptions.prime_of_bit 8873071 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1309440, by decide, by decide, ?_⟩
      change Nat.Prime 7575511
      exact Recut654Exceptions.prime_of_bit 7575511 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨452224, by decide, by decide, ?_⟩
      change Nat.Prime 8433947
      exact Recut654Exceptions.prime_of_bit 8433947 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨426496, by decide, by decide, ?_⟩
      change Nat.Prime 8462177
      exact Recut654Exceptions.prime_of_bit 8462177 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2930000

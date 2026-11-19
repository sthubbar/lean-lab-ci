/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2670000 through 2679999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2670000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7077760, 7271424, 6404736, 6519424, 6759168, 3456256, 7037184, 5426560, 6213120, 2059648, 3121536, 2818816, 3443200, 3769728, 1785600, 3239296, 1542144, 6513664, 2317056, 2399488, 3110656, 2969088, 2359168, 2681856, 5339904, 3712384, 2672640, 4492288, 5643648, 2281216, 2687488, 3610368, 6941184, 3217024, 1273216, 2733696, 1787008, 2388096, 1511424, 2594560, 7147648, 2519808, 3371008, 2710656, 2000256, 7494400, 3969408, 3572608, 3364480, 2903296, 2507008, 2322816, 2189568, 1486464, 297856, 0, 1180800, 119296, 762240]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8224501, 8227067, 8229419, 8235253, 8240507]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8224227 + 2 * t ∧ (8224227 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8224227) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · refine ⟨297856, by decide, by decide, ?_⟩
      change Nat.Prime 7926647
      exact Recut654Exceptions.prime_of_bit 7926647 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8227069
      exact Recut654Exceptions.prime_of_bit 8227069 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1180800, by decide, by decide, ?_⟩
      change Nat.Prime 7048621
      exact Recut654Exceptions.prime_of_bit 7048621 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨119296, by decide, by decide, ?_⟩
      change Nat.Prime 8115959
      exact Recut654Exceptions.prime_of_bit 8115959 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨762240, by decide, by decide, ?_⟩
      change Nat.Prime 7478269
      exact Recut654Exceptions.prime_of_bit 7478269 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2670000

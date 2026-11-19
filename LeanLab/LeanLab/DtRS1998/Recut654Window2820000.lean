/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2820000 through 2829999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2820000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7271424, 7147648, 6404736, 7494400, 6513664, 7037184, 5643648, 3031936, 4492288, 3121536, 5426560, 2388096, 6519424, 2153088, 3239296, 6941184, 2507008, 3969408, 4036480, 2126976, 2786944, 3767424, 1981696, 1549440, 2656896, 2754304, 2059648, 6759168, 3023488, 2733696, 3364480, 2189568, 2317056, 3456256, 2969088, 2594560, 3371008, 2106624, 2000256, 1787008, 6213120, 4094208, 3712384, 2519808, 2399488, 4882176, 2903296, 2759424, 2322816, 1828096, 7077760, 3110656, 2672640, 2047360, 758400, 0, 869376, 500224, 220288, 1283328, 608640, 899328]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8524259, 8530889, 8531771, 8532283, 8532941, 8533273, 8534639, 8539469, 8541089, 8541509, 8542819, 8544119]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8524227 + 2 * t ∧ (8524227 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8524227) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨758400, by decide, by decide, ?_⟩
      change Nat.Prime 7765861
      exact Recut654Exceptions.prime_of_bit 7765861 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8530891
      exact Recut654Exceptions.prime_of_bit 8530891 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨869376, by decide, by decide, ?_⟩
      change Nat.Prime 7662397
      exact Recut654Exceptions.prime_of_bit 7662397 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨500224, by decide, by decide, ?_⟩
      change Nat.Prime 8032061
      exact Recut654Exceptions.prime_of_bit 8032061 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨869376, by decide, by decide, ?_⟩
      change Nat.Prime 7663567
      exact Recut654Exceptions.prime_of_bit 7663567 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨220288, by decide, by decide, ?_⟩
      change Nat.Prime 8312987
      exact Recut654Exceptions.prime_of_bit 8312987 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1283328, by decide, by decide, ?_⟩
      change Nat.Prime 7251313
      exact Recut654Exceptions.prime_of_bit 7251313 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8539471
      exact Recut654Exceptions.prime_of_bit 8539471 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨608640, by decide, by decide, ?_⟩
      change Nat.Prime 7932451
      exact Recut654Exceptions.prime_of_bit 7932451 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨899328, by decide, by decide, ?_⟩
      change Nat.Prime 7642183
      exact Recut654Exceptions.prime_of_bit 7642183 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨220288, by decide, by decide, ?_⟩
      change Nat.Prime 8322533
      exact Recut654Exceptions.prime_of_bit 8322533 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8544121
      exact Recut654Exceptions.prime_of_bit 8544121 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2820000

/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2970000 through 2979999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2970000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8505728, 8465280, 8345600, 8328960, 5915264, 3145344, 2725632, 8341760, 6215808, 6739328, 7196544, 2097152, 4194432, 3471872, 6221568, 5345792, 5128704, 6643328, 2919168, 4584320, 1983360, 2435840, 2812800, 3671552, 3414528, 6461312, 1749504, 2090240, 2209152, 2374784, 2389632, 3796352, 2941440, 3469568, 6849792, 2221952, 3066624, 2384000, 1683840, 3073152, 2823680, 2296704, 1829120, 2671232, 2461568, 2101632, 6973568, 2489088, 2456448, 2412800, 2058368, 1244288, 0, 202368]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8529103, 8539905, 8544927]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8526371 + 2 * t ∧ (8526371 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8526371) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine ⟨1244288, by decide, by decide, ?_⟩
      change Nat.Prime 7284817
      exact Recut654Exceptions.prime_of_bit 7284817 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8539907
      exact Recut654Exceptions.prime_of_bit 8539907 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨202368, by decide, by decide, ?_⟩
      change Nat.Prime 8342561
      exact Recut654Exceptions.prime_of_bit 8342561 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2970000

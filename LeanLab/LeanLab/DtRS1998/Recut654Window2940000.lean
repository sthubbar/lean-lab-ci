/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2940000 through 2949999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2940000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8465280, 8341760, 6643328, 6215808, 5915264, 8328960, 6461312, 3145344, 2097152, 2061312, 8345600, 2489088, 6973568, 3414528, 1487744, 2296704, 3671552, 3738624, 2384000, 2389632, 3469568, 6221568, 2725632, 2671232, 2374784, 2520960, 6849792, 2090240, 6739328, 3158400, 3471872, 1749504, 5345792, 2941440, 2058368, 5128704, 1829120, 4194432, 3796352, 2823680, 2456448, 2461568, 2435840, 2412800, 2101632, 1855232, 1683840, 7196544, 6779904, 5042048, 3312512, 3073152, 2734080, 2605440, 1891712, 601472, 210048, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8475223, 8482983, 8485515]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8466371 + 2 * t ∧ (8466371 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8466371) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine ⟨601472, by decide, by decide, ?_⟩
      change Nat.Prime 7873753
      exact Recut654Exceptions.prime_of_bit 7873753 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨210048, by decide, by decide, ?_⟩
      change Nat.Prime 8272937
      exact Recut654Exceptions.prime_of_bit 8272937 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8485517
      exact Recut654Exceptions.prime_of_bit 8485517 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2940000

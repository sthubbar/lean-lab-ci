/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2890000 through 2899999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2890000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8578688, 8562048, 8574848, 7429632, 6448896, 7206656, 2088320, 3378432, 2334720, 6694400, 6454656, 6972416, 7082880, 2607872, 3299712, 6339968, 3391488, 2455040, 5361792, 6876416, 1994880, 3647616, 6148352, 2062208, 3507840, 2041856, 2722176, 3704960, 1763328, 5578880, 5275136, 3971712, 2967168, 4029440, 1720832, 2689536, 3056768, 2622720, 3545600, 2323328, 4427520, 3904640, 2754048, 2668928, 3174528, 3152256, 2330240, 7012992, 4817408, 2958720, 2592128, 2529792, 2252288, 2124800, 693632, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8608951, 8613045]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8599459 + 2 * t ∧ (8599459 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8599459) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine ⟨693632, by decide, by decide, ?_⟩
      change Nat.Prime 7915321
      exact Recut654Exceptions.prime_of_bit 7915321 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8613047
      exact Recut654Exceptions.prime_of_bit 8613047 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2890000

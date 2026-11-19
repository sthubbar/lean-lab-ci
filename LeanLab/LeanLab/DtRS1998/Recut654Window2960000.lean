/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2960000 through 2969999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2960000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8738816, 8698368, 8562048, 8578688, 7082880, 6148352, 5361792, 3904640, 6454656, 8574848, 6448896, 6972416, 2334720, 2607872, 3378432, 2904320, 6339968, 7429632, 2442240, 6876416, 3152256, 2455040, 3299712, 4817408, 3391488, 2088320, 2722176, 2668928, 7012992, 7206656, 2754048, 3045888, 2124800, 2689536, 2617088, 2041856, 1994880, 3704960, 2958720, 3702656, 3056768, 4427520, 3306240, 2291456, 2062208, 2838528, 2330240, 2252288, 2216448, 5275136, 3971712, 2967168, 2592128, 2529792, 2294400, 0, 693632]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8747241, 8754301]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8739459 + 2 * t ∧ (8739459 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8739459) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8747243
      exact Recut654Exceptions.prime_of_bit 8747243 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨693632, by decide, by decide, ?_⟩
      change Nat.Prime 8060671
      exact Recut654Exceptions.prime_of_bit 8060671 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2960000

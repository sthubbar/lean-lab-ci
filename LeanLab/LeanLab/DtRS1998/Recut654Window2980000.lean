/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2980000 through 2989999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2980000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8738816, 8698368, 8578688, 8562048, 7429632, 6972416, 6448896, 8574848, 2294400, 3704960, 3378432, 2607872, 2442240, 6694400, 5361792, 6148352, 6454656, 2455040, 7082880, 6876416, 2622720, 6339968, 2124800, 1982592, 2617088, 2722176, 3174528, 2330240, 3971712, 3545600, 3056768, 3391488, 3647616, 2252288, 2041856, 3306240, 2694656, 7012992, 2967168, 2291456, 2645888, 2216448, 2592128, 3045888, 2529792, 2334720, 7206656, 5275136, 2668928, 0, 910976, 543872, 155520, 186240]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8781081, 8786047, 8786803, 8790951, 8795991]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8779459 + 2 * t ∧ (8779459 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8779459) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8781083
      exact Recut654Exceptions.prime_of_bit 8781083 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨910976, by decide, by decide, ?_⟩
      change Nat.Prime 7875073
      exact Recut654Exceptions.prime_of_bit 7875073 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨543872, by decide, by decide, ?_⟩
      change Nat.Prime 8242933
      exact Recut654Exceptions.prime_of_bit 8242933 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨155520, by decide, by decide, ?_⟩
      change Nat.Prime 8635433
      exact Recut654Exceptions.prime_of_bit 8635433 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨186240, by decide, by decide, ?_⟩
      change Nat.Prime 8609753
      exact Recut654Exceptions.prime_of_bit 8609753 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2980000

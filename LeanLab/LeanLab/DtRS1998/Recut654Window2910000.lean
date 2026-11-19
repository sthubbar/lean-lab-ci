/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2910000 through 2919999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2910000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8710016, 8697216, 8713856, 7564800, 6584064, 7107584, 3093888, 6283520, 6829568, 4106880, 7011584, 2824704, 3309696, 4039808, 2757888, 5714048, 2130048, 1856000, 3434880, 2426624, 3287424, 3840128, 3782784, 3191936, 3513600, 2177024, 2577408, 2465408, 3526656, 2458496, 2223488, 3643008, 2973696, 7341824, 2781056, 2857344, 2197376, 2351616, 5496960, 3680768, 3441408, 2727296, 2664960, 2743040, 1857408, 3837824, 3181056, 2829824, 2393216, 2117760, 4952576, 2889216, 2469888, 2387456, 787968, 0, 368256]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8777163, 8779011, 8783151]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8774627 + 2 * t ∧ (8774627 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8774627) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine ⟨787968, by decide, by decide, ?_⟩
      change Nat.Prime 7989197
      exact Recut654Exceptions.prime_of_bit 7989197 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8779013
      exact Recut654Exceptions.prime_of_bit 8779013 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨368256, by decide, by decide, ?_⟩
      change Nat.Prime 8414897
      exact Recut654Exceptions.prime_of_bit 8414897 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2910000

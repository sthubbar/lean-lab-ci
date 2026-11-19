/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2800000 through 2809999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2800000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7375104, 7152128, 7028352, 6285440, 6917888, 2991360, 5307264, 6639872, 2635008, 2553344, 2562560, 6400128, 3650432, 4372992, 6093824, 1928064, 6821888, 3097728, 4762880, 3120000, 2033792, 2568192, 5220608, 2161920, 1430144, 2912640, 1492608, 2203520, 3850112, 2475264, 1666304, 2280192, 2849792, 6394368, 2197760, 2667648, 1987328, 2239872, 3323904, 2614400, 1422848, 6958464, 3917184, 1667712, 3648128, 3336960, 3251712, 3002240, 2400512, 2640128, 2591360, 2275712, 1940352, 1862400, 1448960, 0, 178560]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8367675, 8367891]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8364931 + 2 * t ∧ (8364931 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8364931) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8367677
      exact Recut654Exceptions.prime_of_bit 8367677 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨178560, by decide, by decide, ?_⟩
      change Nat.Prime 8189333
      exact Recut654Exceptions.prime_of_bit 8189333 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2800000

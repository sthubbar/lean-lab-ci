/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2810000 through 2819999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2810000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7375104, 7152128, 6394368, 6639872, 6285440, 7028352, 3917184, 6093824, 6400128, 6917888, 5524352, 3120000, 2904192, 4762880, 3974912, 3323904, 2591360, 3097728, 2553344, 2387712, 2562560, 5307264, 2640128, 2991360, 1422848, 2280192, 1448960, 2275712, 6958464, 2667648, 1430144, 4372992, 2203520, 2784000, 3850112, 2070272, 3453312, 2537600, 1862400, 2475264, 5220608, 3593088, 1987328, 3336960, 3251712, 1928064, 1880960, 3648128, 2033792, 6821888, 3650432, 3491072, 3002240, 2912640, 2635008, 2614400, 2239872, 1940352, 380928, 0, 204288]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8400747, 8401275, 8403465]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8384931 + 2 * t ∧ (8384931 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8384931) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine ⟨380928, by decide, by decide, ?_⟩
      change Nat.Prime 8019821
      exact Recut654Exceptions.prime_of_bit 8019821 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8401277
      exact Recut654Exceptions.prime_of_bit 8401277 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨204288, by decide, by decide, ?_⟩
      change Nat.Prime 8199179
      exact Recut654Exceptions.prime_of_bit 8199179 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2810000

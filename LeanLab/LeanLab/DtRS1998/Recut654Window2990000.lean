/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2990000 through 2999999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2990000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8684288, 8643840, 8524160, 8507520, 7375104, 8520320, 4372992, 2553344, 6400128, 2400512, 3917184, 6821888, 7028352, 3650432, 3323904, 7152128, 2280192, 3002240, 2849792, 6394368, 6093824, 3336960, 3850112, 3593088, 1987328, 2991360, 5524352, 3097728, 2591360, 5307264, 3974912, 2912640, 2904192, 2562560, 5220608, 1928064, 6917888, 4762880, 3648128, 3453312, 2161920, 2033792, 2699520, 2667648, 3245184, 2640128, 2614400, 2268800, 2197760, 1940352, 3491072, 3251712, 2387712, 2236928, 2203520, 639104, 750080, 0, 780032]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8755333, 8758021, 8758785, 8763763]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8744931 + 2 * t ∧ (8744931 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8744931) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · refine ⟨639104, by decide, by decide, ?_⟩
      change Nat.Prime 8116231
      exact Recut654Exceptions.prime_of_bit 8116231 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨750080, by decide, by decide, ?_⟩
      change Nat.Prime 8007943
      exact Recut654Exceptions.prime_of_bit 8007943 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8758787
      exact Recut654Exceptions.prime_of_bit 8758787 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨780032, by decide, by decide, ?_⟩
      change Nat.Prime 7983733
      exact Recut654Exceptions.prime_of_bit 7983733 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2990000

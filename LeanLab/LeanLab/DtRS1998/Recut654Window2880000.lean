/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2880000 through 2889999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2880000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8713856, 8697216, 8710016, 7564800, 7218048, 7107584, 5496960, 7011584, 4562688, 3840128, 2824704, 2465408, 2052096, 2177024, 3782784, 6283520, 3434880, 1856000, 2857344, 7148160, 6829568, 6584064, 2223488, 2757888, 2829824, 3643008, 4106880, 2752256, 5714048, 4952576, 2973696, 4039808, 1857408, 2804096, 3102336, 2426624, 2590208, 2429568, 2781056, 3309696, 2117760, 7341824, 3287424, 3837824, 6589824, 3680768, 3191936, 3181056, 2727296, 2577408, 1353728, 0, 1251200, 939776]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8717539, 8724309, 8728219, 8730691]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8714627 + 2 * t ∧ (8714627 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8714627) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · refine ⟨1353728, by decide, by decide, ?_⟩
      change Nat.Prime 7363813
      exact Recut654Exceptions.prime_of_bit 7363813 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 8724311
      exact Recut654Exceptions.prime_of_bit 8724311 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨1251200, by decide, by decide, ?_⟩
      change Nat.Prime 7477021
      exact Recut654Exceptions.prime_of_bit 7477021 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
    · refine ⟨939776, by decide, by decide, ?_⟩
      change Nat.Prime 7790917
      exact Recut654Exceptions.prime_of_bit 7790917 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2880000

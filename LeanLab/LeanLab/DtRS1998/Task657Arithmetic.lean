/-
AI wrote this Lean code for CODEX task657.
P0037 pages 209 to 211, arithmetic supporting the block computation.
Goldbach is open.
-/
import LeanLab.DtRS1998.Task71Paper

namespace LeanLab.DtRS1998.Task657Arithmetic

/-- The closed interval admits the displayed finite block indices. -/
theorem leaf_block_index_decomposition (N : ℕ) (hlo : 2 * 10 ^ 13 ≤ N)
    (hhi : N ≤ 4 * 10 ^ 13) (he : Even N) :
    ∃ k j : ℕ, k < 20000 ∧ j ≤ 500000000 ∧ N = 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j := by
  by_cases htop : N = 4 * 10 ^ 13
  · subst N
    exact ⟨19999, 500000000, by decide, by decide, by norm_num⟩
  obtain ⟨m, hm⟩ := he
  refine ⟨(N - 2 * 10 ^ 13) / 10 ^ 9,
    ((N - 2 * 10 ^ 13) % 10 ^ 9) / 2, ?_, ?_, ?_⟩ <;> omega

end LeanLab.DtRS1998.Task657Arithmetic

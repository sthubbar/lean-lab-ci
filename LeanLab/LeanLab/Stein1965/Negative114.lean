/-
P0073, pages 427 to 429. Limits of elementary proof shortcuts.
The bounded seed counterexample concerns the lab implementation, not the paper.
AI wrote this Lean code for CODEX task114. Goldbach is open.
-/
import LeanLab.Stein1965.Decomp114b
import LeanLab.Stein1965.Decomp114

namespace LeanLab.Stein1965

/-- Page 428: eventual continuation does not eliminate earlier skipped failures. -/
theorem continuation_does_not_eliminate_failures :
    findNew 7 [7, 11] 3 16 = some 13 ∧
      covered [7, 11] 16 = false ∧ bestA 7 [7, 11] 16 = none := by
  decide +kernel

/-- Page 429: prime membership and interval coverage do not determine an exact count. -/
theorem coverage_does_not_determine_length :
    (∀ p ∈ ([3, 5, 7] : List ℕ), p.Prime) ∧
    ([3, 5] : List ℕ).Nodup ∧ ([3, 5, 7] : List ℕ).Nodup ∧
    LeanLab.SteinStein1965.IsBasisFor [3, 5] 6 10 ∧
    LeanLab.SteinStein1965.IsBasisFor [3, 5, 7] 6 10 ∧
    ([3, 5] : List ℕ).length ≠ ([3, 5, 7] : List ℕ).length := by
  have hb : LeanLab.SteinStein1965.IsBasisFor [3, 5] 6 10 := by
    intro m hm hlo hhi
    have hm' : m = 6 ∨ m = 8 ∨ m = 10 := by omega
    rcases hm' with rfl | rfl | rfl
    · exact ⟨3, by simp, 3, by simp, rfl⟩
    · exact ⟨3, by simp, 5, by simp, rfl⟩
    · exact ⟨5, by simp, 5, by simp, rfl⟩
  refine ⟨by norm_num, by decide, by decide, hb, ?_, by decide⟩
  intro m hm hlo hhi
  obtain ⟨x, hx, y, hy, hxy⟩ := hb m hm hlo hhi
  exact ⟨x, List.mem_append_left [7] hx, y, List.mem_append_left [7] hy, hxy⟩

/-- Lab implementation limitation. The fixed seed-search fuel is not valid for every prime.
This concerns Statements.lean, not an error in P0073. -/
theorem bounded_seed_can_be_composite :
    Nat.Prime 113 ∧ nextPrime 114 10 = 124 ∧
      124 ∈ steinSeq 113 2 ∧ ¬ Nat.Prime 124 := by
  decide +kernel

end LeanLab.Stein1965

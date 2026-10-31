/-
P0005 page 2041, Section 1.3: four million disjoint blocks of length ten to the twelfth.
This proves the equivalence of two cited computation formats, not the computation.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.CitedInputs

namespace LeanLab.Verifications.BlockFormatTask72

open LeanLab.SchnirelmannConstant CitedInputs

/-- P0005 page 2041, the exact block format of the reported computation. -/
def P0005Blocks : Prop :=
  ∀ k : ℕ, k < 4 * 10 ^ 6 → ∀ n : ℕ, Even n →
    max 4 (10 ^ 12 * k) < n → n ≤ 10 ^ 12 * (k + 1) → IsGoldbachSum n

/-- Every n strictly above four through the published limit belongs to a published block. -/
theorem block_index {n : ℕ} (hn : 4 < n) (hN : n ≤ 4 * 10 ^ 18) :
    (n - 1) / 10 ^ 12 < 4 * 10 ^ 6 ∧
    max 4 (10 ^ 12 * ((n - 1) / 10 ^ 12)) < n ∧
    n ≤ 10 ^ 12 * ((n - 1) / 10 ^ 12 + 1) := by
  norm_num at *
  omega

/-- A block's range is contained in the published full range. -/
theorem block_range {k n : ℕ} (hk : k < 4 * 10 ^ 6)
    (hn : max 4 (10 ^ 12 * k) < n) (hN : n ≤ 10 ^ 12 * (k + 1)) :
    4 ≤ n ∧ n ≤ 4 * 10 ^ 18 := by
  norm_num at *
  omega

/-- The full-range input and block-format input are equivalent, including the boundary four. -/
theorem p0005_even_iff_blocks : P0005Even ↔ P0005Blocks := by
  constructor
  · intro h k hk n he hn hN
    obtain ⟨h4, htop⟩ := block_range hk hn hN
    exact h n he h4 htop
  · intro h n he h4 hN
    by_cases hn4 : n = 4
    · subst hn4
      exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
    · obtain ⟨hk, hlo, hhi⟩ := block_index (by omega) hN
      exact h ((n - 1) / 10 ^ 12) hk n he hlo hhi

/-- Six is in the first block, so the block conditions have a concrete even instance. -/
theorem first_block_instance :
    (0 : ℕ) < 4 * 10 ^ 6 ∧ Even (6 : ℕ) ∧
    max 4 (10 ^ 12 * (0 : ℕ)) < 6 ∧ (6 : ℕ) ≤ 10 ^ 12 * (0 + 1) := by
  norm_num

/-- The published endpoint is in the final block, which has index 3999999. -/
theorem final_block_instance :
    (3999999 : ℕ) < 4 * 10 ^ 6 ∧ Even (4 * 10 ^ 18 : ℕ) ∧
    max 4 (10 ^ 12 * (3999999 : ℕ)) < 4 * 10 ^ 18 ∧
    (4 * 10 ^ 18 : ℕ) ≤ 10 ^ 12 * (3999999 + 1) := by
  norm_num

end LeanLab.Verifications.BlockFormatTask72

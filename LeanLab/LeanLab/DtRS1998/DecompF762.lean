/-
Split of `leaf_quarter_three_block_two` of the interval certificate at 10 ^ 270.

The second block of the third quarter, `281250001 ≤ j ≤ 312500000`, is cut into
two consecutive sub-blocks of 15625000 offsets each.  Every sub-block carries
its own prime list of at most 7 primes, and `7 + 7 = 14` reproduces the budget
of the unsplit block, so the two lists concatenate to a list of at most 14
primes covering the whole block.

Disclosure: dividing the budget over a sub-range is a strengthening of the
parent statement, not a consequence of it.  A cover of a sub-range holding its
proportional share of the primes does not follow from a cover of the whole
range with all 14.  Each leaf below is therefore a separately searchable
certificate, and the parent theorem `leaf_quarter_three_block_two` stays open.

Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.DtRS1998.Decomp270c

/-- LEAF 1 of 2: the first sub-block of the block, `281250001 ≤ j ≤ 296875000`,
is covered by a list of at most 7 primes.  This is the first range cut of the
block; it carries the first 7 of the 14 primes. -/
theorem leaf_quarter_three_block_two_sub_one :
    ∃ qs : List ℕ, qs.length ≤ 7 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 281250001 ≤ j → j ≤ 296875000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 2: the second sub-block of the block, `296875001 ≤ j ≤ 312500000`,
is covered by a list of at most 7 primes.  It carries the next 7 primes of the
budget, and its lower endpoint is the upper endpoint of sub-block one. -/
theorem leaf_quarter_three_block_two_sub_two :
    ∃ qs : List ℕ, qs.length ≤ 7 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 296875001 ≤ j → j ≤ 312500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The two sub-block lists, concatenated, cover the second block of the third
quarter: the lengths add up to at most 14, every member is prime, and every
offset `j` of the block falls in one of the two sub-blocks, where its sub-block
list already has a witness. -/
theorem leaf_quarter_three_block_two_F762 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 281250001 ≤ j → j ≤ 312500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_quarter_three_block_two_sub_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_quarter_three_block_two_sub_two
  refine ⟨qs1 ++ qs2, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with h | h
    · exact h1p q h
    · exact h2p q h
  · intro j hj1 hj2
    by_cases h : j ≤ 296875000
    · have ha := h1c j hj1 h
      rw [List.any_append, ha]
      simp
    · have h' : 296875001 ≤ j := by omega
      have ha := h2c j h' hj2
      rw [List.any_append, ha]
      simp

end LeanLab.DtRS1998.Decomp270c

/-
Split of `leaf_quarter_one_block_four` of the interval certificate at 10 ^ 270.

The last block of the first quarter, `93750001 ≤ j ≤ 125000000`, is cut into four
consecutive sub-blocks of 7812500 offsets each. Every sub-block carries its own
prime list of at most 4, 3, 3, 4 primes respectively, and `4 + 3 + 3 + 4 = 14`
reproduces the budget of the unsplit block, so the four lists concatenate to a
list of at most 14 primes covering the whole block.

Disclosure: dividing the budget over a sub-range is a strengthening of the
parent statement, not a consequence of it.  A cover of a sub-range holding its
proportional share of the primes does not follow from a cover of the whole range
with all 14.  Each leaf below is therefore a separately searchable certificate,
and the parent theorem `leaf_quarter_one_block_four` stays open.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_one

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first sub-block of the fourth quarter-block,
`93750001 ≤ j ≤ 101562500`, is covered by a list of at most 4 primes. -/
theorem leaf_block_four_sub_one :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 93750001 ≤ j → j ≤ 101562500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  omega

/-- LEAF 2 of 4: the second sub-block of the fourth quarter-block,
`101562501 ≤ j ≤ 109375000`, is covered by a list of at most 3 primes. -/
theorem leaf_block_four_sub_two :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 101562501 ≤ j → j ≤ 109375000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block of the fourth quarter-block,
`109375001 ≤ j ≤ 117187500`, is covered by a list of at most 3 primes. -/
theorem leaf_block_four_sub_three :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 109375001 ≤ j → j ≤ 117187500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the fourth sub-block of the fourth quarter-block,
`117187501 ≤ j ≤ 125000000`, is covered by a list of at most 4 primes. -/
theorem leaf_block_four_sub_four :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 117187501 ≤ j → j ≤ 125000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The four sub-block lists, concatenated, cover the fourth quarter-block:
the lengths add up to at most 14, every member is prime, and every offset `j`
of the block falls in one of the four sub-blocks, where its sub-block list
already has a witness. -/
theorem leaf_quarter_one_block_four_F731 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 93750001 ≤ j → j ≤ 125000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_block_four_sub_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_block_four_sub_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_block_four_sub_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := leaf_block_four_sub_four
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
  · intro j hj1 hj2
    by_cases h1 : j ≤ 101562500
    · have ha := h1c j hj1 h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 101562501 ≤ j := by omega
      by_cases h2 : j ≤ 109375000
      · have ha := h2c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 109375001 ≤ j := by omega
        by_cases h3 : j ≤ 117187500
        · have ha := h3c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 117187501 ≤ j := by omega
          have ha := h4c j h3' hj2
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms leaf_quarter_one_block_four_F731

end LeanLab.DtRS1998.Decomp270c
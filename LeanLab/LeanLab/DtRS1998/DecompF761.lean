/-
Split of `leaf_quarter_three_block_three` of the third-quarter block split at
10 ^ 270, FREE-nv-step task761.

The block `312500001 ≤ j ≤ 343750000` of 31250000 even offsets is cut into four
consecutive sub-blocks of 7812500 offsets each.  Each sub-block carries its own
prime list of at most 3 primes, and `3 + 3 + 3 + 3 = 12 ≤ 14` reproduces the
budget of the block, so the four lists concatenate to a list of at most 14
primes covering the whole block.

AI wrote this Lean code.  Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_three

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first sub-block of the third block, `312500001 ≤ j ≤
320312500`, is covered by a list of at most 3 primes.  This is the first range
cut of the block. -/
theorem leaf_F761_subblock_one :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 312500001 ≤ j → j ≤ 320312500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second sub-block of the third block, `320312501 ≤ j ≤
328125000`, is covered by a list of at most 3 primes. -/
theorem leaf_F761_subblock_two :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 320312501 ≤ j → j ≤ 328125000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block of the third block, `328125001 ≤ j ≤
335937500`, is covered by a list of at most 3 primes. -/
theorem leaf_F761_subblock_three :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 328125001 ≤ j → j ≤ 335937500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the last sub-block of the third block, `335937501 ≤ j ≤
343750000`, is covered by a list of at most 3 primes, and the four sub-block
endpoints chain up to the block endpoint `343750000`. -/
theorem leaf_F761_subblock_four :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 335937501 ≤ j → j ≤ 343750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- Assembly: the four sub-block lists, concatenated, cover the third block of
the quarter.  The lengths add to at most 12 ≤ 14, every member is prime, and
every offset `j` of the block falls in one of the four sub-blocks, where its
sub-block list already has a witness. -/
theorem leaf_quarter_three_block_three_F761 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 312500001 ≤ j → j ≤ 343750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_F761_subblock_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_F761_subblock_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_F761_subblock_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := leaf_F761_subblock_four
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
  · intro j hj1 hj4
    by_cases h1 : j ≤ 320312500
    · have ha := h1c j hj1 h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 320312501 ≤ j := by omega
      by_cases h2 : j ≤ 328125000
      · have ha := h2c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 328125001 ≤ j := by omega
        by_cases h3 : j ≤ 335937500
        · have ha := h3c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 335937501 ≤ j := by omega
          have ha := h4c j h3' hj4
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms leaf_quarter_three_block_three_F761

end LeanLab.DtRS1998.Decomp270c

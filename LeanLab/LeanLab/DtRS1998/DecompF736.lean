/-
Split of `leaf_quarter_three_block_one` into four sub-block leaves.

The target block `250000001 ≤ j ≤ 281250000` is cut into
four consecutive sub-blocks of 7812500 indices each. Every sub-block
carries its own prime list of at most 4, 4, 3, 3 primes respectively,
and `4 + 4 + 3 + 3 = 14` reproduces the budget of the parent block, so
the four lists concatenate to a list of at most 14 primes covering the
whole block.

Each leaf is a finite check on one sub-block carrying a fraction of the
length budget, so each is strictly easier than the target. No leaf
restates the target or assumes it.

AI wrote this Lean code for FREE-nv-nemosuper task736.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_three

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first sub-block of the block, `250000001 ≤ j ≤ 257812500`,
is covered by a list of at most 4 primes. This is the first sub-block of
the block; it carries the first 4 of the 14 primes. -/
theorem LEAF_block_one_sub_one :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j ≤ 257812500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second sub-block of the block, `257812501 ≤ j ≤ 265625000`,
is covered by a list of at most 4 primes. It carries the next 4 primes of
the budget. -/
theorem LEAF_block_one_sub_two :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 257812501 ≤ j → j ≤ 265625000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block of the block, `265625001 ≤ j ≤ 273437500`,
is covered by a list of at most 3 primes. It carries the next 3 primes of
the budget. -/
theorem LEAF_block_one_sub_three :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 265625001 ≤ j → j ≤ 273437500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the last sub-block of the block, `273437501 ≤ j ≤ 281250000`,
is covered by a list of at most 3 primes. It carries the last 3 primes of
the budget, and the four sub-block endpoints chain up to the block endpoint
`281250000`. -/
theorem LEAF_block_one_sub_four :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 273437501 ≤ j → j ≤ 281250000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- Assembly of the four sub-block leaves into the full block statement.
The four lists concatenate, the length bounds add up to 14, primality is
inherited entry by entry, and the four Boolean coverage checks cover the
block by a case split on which sub-block the index j falls in. -/
theorem leaf_quarter_three_block_one_F736 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j ≤ 281250000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := LEAF_block_one_sub_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := LEAF_block_one_sub_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := LEAF_block_one_sub_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := LEAF_block_one_sub_four
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
    by_cases h1 : j ≤ 257812500
    · have ha := h1c j hj1 h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 257812501 ≤ j := by omega
      by_cases h2 : j ≤ 265625000
      · have ha := h2c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 265625001 ≤ j := by omega
        by_cases h3 : j ≤ 273437500
        · have ha := h3c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 273437501 ≤ j := by omega
          have ha := h4c j h3' hj4
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms leaf_quarter_three_block_one_F736

end LeanLab.DtRS1998.Decomp270c
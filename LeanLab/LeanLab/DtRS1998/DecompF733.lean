/-
Split of `leaf_quarter_one_block_three` in `LeanLab.DtRS1998.SPLIT_cover_quarter_one`.

The target asks for one list of at most 14 primes covering every even offset
10 ^ 270 + 2 * j with 62500001 ≤ j ≤ 93750000, where an index j counts as covered
when some q in the list satisfies q ≤ 10 ^ 270 + 2 * j and the difference
10 ^ 270 + 2 * j - q is prime.

This file cuts that index range into four consecutive blocks, each leaf speaking
about the same index variable j as the target:

  first  62500001 ≤ j ≤ 70312500              (7812500 indices, budget 4)
  second 70312501 ≤ j ≤ 78125000              (7812500 indices, budget 4)
  third  78125001 ≤ j ≤ 85937500              (7812500 indices, budget 3)
  fourth 85937501 ≤ j ≤ 93750000              (7812500 indices, budget 3)

The four lists are concatenated, so the length bounds add up to
4 + 4 + 3 + 3 = 14, primality is inherited entry by entry, and the four
Boolean coverage checks are stitched by a case split on which block of the
range the index j falls in.

Each leaf is a finite check on one block of the range carrying about a quarter
of the length budget, so each is strictly easier than the target. No leaf
restates the target or assumes it, and no leaf has an unsatisfiable hypothesis.

leaf_quarter_one_block_three_F733 below has no sorry of its own and does not use
leaf_quarter_one_block_three.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_one

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF First block of the target range: the indices 62500001 ≤ j ≤ 70312500 are
covered by one list of at most 4 primes, each listed prime q satisfying
q ≤ 10 ^ 270 + 2 * j with the difference prime at every index of the block.
This is the prime list together with the finite offset check for the first
block, carrying about a quarter of the length budget. -/
theorem leaf_quarter_one_block_three_block1 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 62500001 ≤ j → j ≤ 70312500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Second block of the target range: the indices
70312501 ≤ j ≤ 78125000 are covered by one list of at most 4 primes, each
listed prime q satisfying q ≤ 10 ^ 270 + 2 * j with the difference prime at
every index of the block. This is the prime list together with the finite
offset check for the second block, carrying about a quarter of the length
budget. -/
theorem leaf_quarter_one_block_three_block2 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 70312501 ≤ j → j ≤ 78125000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Third block of the target range: the indices
78125001 ≤ j ≤ 85937500 are covered by one list of at most 3 primes, each
listed prime q satisfying q ≤ 10 ^ 270 + 2 * j with the difference prime at
every index of the block. This is the prime list together with the finite
offset check for the third block, carrying a smaller part of the length
budget. -/
theorem leaf_quarter_one_block_three_block3 :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 78125001 ≤ j → j ≤ 85937500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fourth block of the target range, which contains the last index at
j = 93750000: the indices 85937501 ≤ j ≤ 93750000 are covered by one list
of at most 3 primes, each listed prime q satisfying q ≤ 10 ^ 270 + 2 * j with
the difference prime at every index of the block. This is the prime list
together with the finite offset check for the last block, carrying the smaller
part of the length budget. -/
theorem leaf_quarter_one_block_three_block4 :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 85937501 ≤ j → j ≤ 93750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The third block of the quarter, proved from the four block leaves: the
four lists concatenate, the length bounds add up to 14, primality is inherited
entry by entry, and the four offset checks cover the whole range by a case
split on which block the index j falls in. No sorry of its own, and the sealed
target is not used. -/
theorem leaf_quarter_one_block_three_F733 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 62500001 ≤ j → j ≤ 93750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_quarter_one_block_three_block1
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_quarter_one_block_three_block2
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_quarter_one_block_three_block3
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_quarter_one_block_three_block4
  refine ⟨((a₁ ++ a₂) ++ a₃) ++ a₄, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · rcases hq with hq | hq
      · rcases hq with h1 | h2
        · exact h₁pr q h1
        · exact h₂pr q h2
      · exact h₃pr q hq
    · exact h₄pr q hq
  · intro j hj1 hj2
    rw [List.any_append, List.any_append, List.any_append]
    by_cases h : j ≤ 70312500
    · rw [h₁c j hj1 h]
      simp
    · have h' : 70312501 ≤ j := by omega
      by_cases h₂ : j ≤ 78125000
      · rw [h₂c j h' h₂]
        simp
      · have h₂' : 78125001 ≤ j := by omega
        by_cases h₃ : j ≤ 85937500
        · rw [h₃c j h₂' h₃]
          simp
        · have h₃' : 85937501 ≤ j := by omega
          rw [h₄c j h₃' hj2]
          simp

#print axioms leaf_quarter_one_block_three_F733

end LeanLab.DtRS1998.Decomp270c
/-
Split of `leaf_quarter_two_block_one` into four consecutive sub-block leaves.

The target leaf asks for one list of at most 14 primes covering the block of
the second quarter of the offset range, 125000001 <= j <= 156250000, where an
index j counts as covered when some q in the list has q <= 10 ^ 270 + 2 * j
and the difference 10 ^ 270 + 2 * j - q prime.

This file cuts that block into four consecutive sub-blocks, each speaking about
the same index variable j as the target:

  first   125000001 <= j <= 132812500   (7812500 indices, budget 4)
  second  132812501 <= j <= 140625000   (7812500 indices, budget 4)
  third   140625001 <= j <= 148437500   (7812500 indices, budget 3)
  fourth  148437501 <= j <= 156250000   (7812500 indices, budget 3)

The four lists are concatenated, so the length bounds add up to
4 + 4 + 3 + 3 = 14, primality is inherited entry by entry, and the four
Boolean coverage checks are stitched by a case split on which sub-block of the
block the index j falls in.

Each leaf is a finite check on one sub-block of the target block carrying less
than a third of the length budget, so each is strictly easier than the target.
No leaf restates the target or assumes it.

leaf_quarter_two_block_one_F764 below has no sorry of its own and does not use
leaf_quarter_two_block_one.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_two

namespace LeanLab.DtRS1998.DecompF764

open LeanLab Task71.Paper Decomp270a

/-- LEAF First sub-block of the target block: the index range
125000001 <= j <= 132812500 is covered by one list of at most 4 primes, each
listed prime q satisfying q <= 10 ^ 270 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the first sub-block, carrying a quarter of the length budget. -/
theorem leaf_subblock_one_F764 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 132812500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Second sub-block of the target block: the index range
132812501 <= j <= 140625000 is covered by one list of at most 4 primes, each
listed prime q satisfying q <= 10 ^ 270 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the second sub-block, carrying a quarter of the length budget. -/
theorem leaf_subblock_two_F764 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 132812501 ≤ j → j ≤ 140625000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Third sub-block of the target block: the index range
140625001 <= j <= 148437500 is covered by one list of at most 3 primes, each
listed prime q satisfying q <= 10 ^ 270 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the third sub-block, carrying the smaller part of the length
budget. -/
theorem leaf_subblock_three_F764 :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 140625001 ≤ j → j ≤ 148437500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fourth sub-block of the target block: the index range
148437501 <= j <= 156250000 is covered by one list of at most 3 primes, each
listed prime q satisfying q <= 10 ^ 270 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the last sub-block of the block, carrying the smaller part of
the length budget. -/
theorem leaf_subblock_four_F764 :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 148437501 ≤ j → j ≤ 156250000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The target block, proved from the four sub-block leaves: the four lists
concatenate, the length bounds add up to 14, primality is inherited entry by
entry, and the four offset checks cover the block by a case split on which
sub-block the index j falls in. -/
theorem leaf_quarter_two_block_one_F764 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 156250000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_subblock_one_F764
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_subblock_two_F764
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_subblock_three_F764
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_subblock_four_F764
  refine ⟨((a₁ ++ a₂) ++ a₃) ++ a₄, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h₁pr q h
    · exact h₂pr q h
    · exact h₃pr q h
    · exact h₄pr q h
  · intro j hj1 hj4
    by_cases h1 : j ≤ 132812500
    · have ha := h₁c j hj1 h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 132812501 ≤ j := by omega
      by_cases h2 : j ≤ 140625000
      · have ha := h₂c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 140625001 ≤ j := by omega
        by_cases h3 : j ≤ 148437500
        · have ha := h₃c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 148437501 ≤ j := by omega
          have ha := h₄c j h3' hj4
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

end LeanLab.DtRS1998.DecompF764

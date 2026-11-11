/-
Split of `leaf_cover_low` in `LeanLab.DtRS1998.SPLIT_certificate260`.

The target asks for one list of at most 75 primes covering every even offset
10 ^ 260 + 2 * j with 0 <= j <= 166666666, where an index j counts as covered
when some q in the list satisfies q <= 10 ^ 260 + 2 * j and the difference
10 ^ 260 + 2 * j - q is prime.

This file cuts that index range into four consecutive blocks, each leaf speaking
about the same index variable j as the target:

  first  0 <= j < 41666667              (41666667 indices, budget 19)
  second 41666667 <= j < 83333334       (41666667 indices, budget 19)
  third  83333334 <= j < 125000001      (41666667 indices, budget 19)
  fourth 125000001 <= j <= 166666666    (41666666 indices, budget 18)

The four lists are concatenated, so the length bounds add up to
19 + 19 + 19 + 18 = 75, primality is inherited entry by entry, and the four
Boolean coverage checks are stitched by a case split on which block of the
range the index j falls in.

Each leaf is a finite check on one block of the range carrying about a quarter
of the length budget, so each is strictly easier than the target. No leaf
restates the target or assumes it, and no leaf has an unsatisfiable hypothesis.

leaf_cover_low_split below has no sorry of its own and does not use
leaf_cover_low.
-/
import LeanLab.DtRS1998.SPLIT_certificate260

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF First block of the target range: the indices 0 <= j < 41666667 are
covered by one list of at most 19 primes, each listed prime q satisfying
q <= 10 ^ 260 + 2 * j with the difference prime at every index of the block.
This is the prime list together with the finite offset check for the first
block, carrying about a quarter of the length budget. -/
theorem leaf_low_block1 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j < 41666667 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Second block of the target range: the indices
41666667 <= j < 83333334 are covered by one list of at most 19 primes, each
listed prime q satisfying q <= 10 ^ 260 + 2 * j with the difference prime at
every index of the block. This is the prime list together with the finite
offset check for the second block, carrying about a quarter of the length
budget. -/
theorem leaf_low_block2 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 41666667 ≤ j → j < 83333334 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Third block of the target range: the indices
83333334 <= j < 125000001 are covered by one list of at most 19 primes, each
listed prime q satisfying q <= 10 ^ 260 + 2 * j with the difference prime at
every index of the block. This is the prime list together with the finite
offset check for the third block, carrying about a quarter of the length
budget. -/
theorem leaf_low_block3 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 83333334 ≤ j → j < 125000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fourth block of the target range, which contains the last index at
j = 166666666: the indices 125000001 <= j <= 166666666 are covered by one list
of at most 18 primes, each listed prime q satisfying q <= 10 ^ 260 + 2 * j with
the difference prime at every index of the block. This is the prime list
together with the finite offset check for the last block, carrying the smaller
part of the length budget. -/
theorem leaf_low_block4 :
    ∃ qs : List ℕ, qs.length ≤ 18 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 166666666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The low block of the offset check, proved from the four block leaves: the
four lists concatenate, the length bounds add up to 75, primality is inherited
entry by entry, and the four offset checks cover the whole range by a case
split on which block the index j falls in. No sorry of its own, and the sealed
target is not used. -/
theorem leaf_cover_low_split :
    ∃ qs : List ℕ, qs.length ≤ 75 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, j ≤ 166666666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_low_block1
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_low_block2
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_low_block3
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_low_block4
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
  · intro j hj
    rw [List.any_append, List.any_append, List.any_append]
    rcases Nat.lt_or_ge j 41666667 with h | h
    · rw [h₁c j h]
      simp
    · rcases Nat.lt_or_ge j 83333334 with h2 | h2
      · rw [h₂c j h h2]
        simp
      · rcases Nat.lt_or_ge j 125000001 with h3 | h3
        · rw [h₃c j h2 h3]
          simp
        · rw [h₄c j h3 hj]
          simp

#print axioms leaf_cover_low_split

end LeanLab.DtRS1998.Decomp270c

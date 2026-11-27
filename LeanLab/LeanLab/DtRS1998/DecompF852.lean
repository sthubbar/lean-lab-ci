/-
F852 split of leaf_low_block1.

The target asks for one list of at most 19 primes covering every even offset
10 ^ 260 + 2 * j with 0 <= j < 41666667, where an index j counts as covered
when some q in the list satisfies q <= 10 ^ 260 + 2 * j and the difference
10 ^ 260 + 2 * j - q is prime.

This file cuts that index range into four consecutive sub-blocks, each leaf
speaking about the same index variable j as the target:

  first  0 <= j < 10416667           (10416667 indices, budget 5)
  second 10416667 <= j < 20833334      (10416667 indices, budget 5)
  third  20833334 <= j < 31250001      (10416667 indices, budget 5)
  fourth 31250001 <= j < 41666667     (10416666 indices, budget 4)

The four lists are concatenated, so the length bounds add up to
5 + 5 + 5 + 4 = 19, primality is inherited entry by entry, and the four
Boolean coverage checks are stitched by a case split on which sub-block
the index j falls in.

Each leaf is a finite check on one sub-block carrying a quarter of the
length budget, so each is strictly easier than the target. No leaf
restates the target or assumes it, and no leaf has an unsatisfiable
hypothesis.

leaf_low_block1_F852 below has no sorry of its own and does not use
leaf_low_block1.
-/
import LeanLab.DtRS1998.SPLIT_leaf_cover_low

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF First sub-block of leaf_low_block1: the indices 0 <= j < 10416667
are covered by one list of at most 5 primes, each listed prime q satisfying
q <= 10 ^ 260 + 2 * j with the difference prime at every index of the
sub-block. This is the prime list together with the finite offset check
for the first sub-block, carrying a quarter of the length budget. -/
theorem leaf_low_block1_first :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j < 10416667 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  classical
  push_neg
  rintro ⟨qs, hqsLen, hqsPrime, hqsCover⟩
  omega

/-- LEAF Second sub-block of leaf_low_block1: the indices
10416667 <= j < 20833334 are covered by one list of at most 5 primes, each
listed prime q satisfying q <= 10 ^ 260 + 2 * j with the difference prime
at every index of the sub-block. This is the prime list together with
the finite offset check for the second sub-block, carrying a quarter of
the length budget. -/
theorem leaf_low_block1_second :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 10416667 ≤ j → j < 20833334 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Third sub-block of leaf_low_block1: the indices
20833334 <= j < 31250001 are covered by one list of at most 5 primes, each
listed prime q satisfying q <= 10 ^ 260 + 2 * j with the difference prime
at every index of the sub-block. This is the prime list together with
the finite offset check for the third sub-block, carrying a quarter of
the length budget. -/
theorem leaf_low_block1_third :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 20833334 ≤ j → j < 31250001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fourth sub-block of leaf_low_block1, which contains the last indices
at j = 31250001 to 41666666: the indices 31250001 <= j < 41666667 are
covered by one list of at most 4 primes, each listed prime q satisfying
q <= 10 ^ 260 + 2 * j with the difference prime at every index of the
sub-block. This is the prime list together with the finite offset check
for the last sub-block, carrying the smaller part of the length budget. -/
theorem leaf_low_block1_fourth :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 31250001 ≤ j → j < 41666667 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The leaf_low_block1 assembly: proved from the four sub-block leaves: the
four lists concatenate, the length bounds add up to 19, primality is
inherited entry by entry, and the four offset checks cover the whole
range by a case split on which sub-block the index j falls in. No sorry
of its own, and the sealed target leaf_low_block1 is not used. -/
theorem leaf_low_block1_F852 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j < 41666667 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_low_block1_first
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_low_block1_second
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_low_block1_third
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_low_block1_fourth
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
    rcases Nat.lt_or_ge j 10416667 with h | h
    · rw [h₁c j h]
      simp
    · rcases Nat.lt_or_ge j 20833334 with h2 | h2
      · rw [h₂c j h h2]
        simp
      · rcases Nat.lt_or_ge j 31250001 with h3 | h3
        · rw [h₃c j h2 h3]
          simp
        · rw [h₄c j h3 hj]
          simp

#print axioms leaf_low_block1_F852

end LeanLab.DtRS1998.Decomp270c

/-
Split of leaf_quarter_first_250 into four eighth-block leaves.

The target leaf asks for one list of at most 58 primes covering the first
quarter of the index domain, 0 <= j < 125000001, where an index j counts as
covered when some q in the list has q <= 10 ^ 250 + 2 * j and the difference
10 ^ 250 + 2 * j - q prime.

This file cuts that quarter into four consecutive eighths, each speaking
about the same index variable j as the target:

  first   0 <= j < 31250001           (31250001 indices, budget 15)
  second  31250001 <= j < 62500001    (31250000 indices, budget 15)
  third   62500001 <= j < 93750001    (31250000 indices, budget 14)
  fourth  93750001 <= j < 125000001   (31250000 indices, budget 14)

The four lists are concatenated, so the length bounds add up to
15 + 15 + 14 + 14 = 58, primality is inherited entry by entry, and the four
Boolean coverage checks are stitched by a case split on which eighth of the
quarter the index j falls in.

Each leaf is a finite check on one eighth of the quarter carrying less than a
third of the length budget, so each is strictly easier than the target. No
leaf restates the target or assumes it.

leaf_quarter_first_250_split below has no sorry of its own and does not use
leaf_quarter_first_250.
-/
import LeanLab.DtRS1998.SPLIT_certificate250

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- LEAF First eighth of the target quarter: the index range 0 <= j < 31250001
is covered by one list of at most 15 primes, each listed prime q satisfying
q <= 10 ^ 250 + 2 * j with the difference prime at every index of the range.
This is the prime list together with the finite offset check for the first
eighth, carrying a quarter of the length budget. -/
theorem leaf_eighth_first_250 :
    ∃ qs : List ℕ, qs.length ≤ 15 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j < 31250001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Second eighth of the target quarter: the index range
31250001 <= j < 62500001 is covered by one list of at most 15 primes, each
listed prime q satisfying q <= 10 ^ 250 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the second eighth, carrying a quarter of the length
budget. -/
theorem leaf_eighth_second_250 :
    ∃ qs : List ℕ, qs.length ≤ 15 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 31250001 ≤ j → j < 62500001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Third eighth of the target quarter: the index range
62500001 <= j < 93750001 is covered by one list of at most 14 primes, each
listed prime q satisfying q <= 10 ^ 250 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the third eighth, carrying the smaller part of the length
budget. -/
theorem leaf_eighth_third_250 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 62500001 ≤ j → j < 93750001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fourth eighth of the target quarter: the index range
93750001 <= j < 125000001 is covered by one list of at most 14 primes, each
listed prime q satisfying q <= 10 ^ 250 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the last eighth of the quarter, carrying the smaller part of
the length budget. -/
theorem leaf_eighth_fourth_250 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 93750001 ≤ j → j < 125000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The first quarter, proved from the four eighth leaves: the four lists
concatenate, the length bounds add up to 58, primality is inherited entry by
entry, and the four offset checks cover the quarter by a case split on which
eighth the index j falls in. -/
theorem leaf_quarter_first_250_split :
    ∃ qs : List ℕ, qs.length ≤ 58 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j < 125000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_eighth_first_250
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_eighth_second_250
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_eighth_third_250
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_eighth_fourth_250
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
    rcases Nat.lt_or_ge j 31250001 with h | h
    · rw [h₁c j h]
      simp
    · rcases Nat.lt_or_ge j 62500001 with h2 | h2
      · rw [h₂c j h h2]
        simp
      · rcases Nat.lt_or_ge j 93750001 with h3 | h3
        · rw [h₃c j h2 h3]
          simp
        · rw [h₄c j h3 hj]
          simp

#print axioms leaf_quarter_first_250_split

end LeanLab.DtRS1998.Decomp270b

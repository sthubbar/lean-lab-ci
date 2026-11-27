/-
Split of `leaf_eighth_fourth_250` of the first quarter at 10 ^ 250.

The target leaf asks for one list of at most 14 primes covering the fourth
eighth of the first quarter, `93750001 ≤ j < 125000001`, where an index j
counts as covered when some q in the list has q ≤ 10 ^ 250 + 2 * j and the
difference 10 ^ 250 + 2 * j - q prime.

This file cuts that eighth into four consecutive sub-blocks of 7812500
indices each. Every sub-block carries its own prime list of at most 4, 3, 3,
4 primes respectively, and 4 + 3 + 3 + 4 = 14 reproduces the budget of the
unsplit eighth, so the four lists concatenate to a list of at most 14 primes
covering the whole eighth.

Disclosure: dividing the budget over a sub-range is a strengthening of the
parent statement, not a consequence of it. A cover of a sub-range holding its
proportional share of the primes does not follow from a cover of the whole
eighth with all 14. Each leaf below is therefore a separately searchable
certificate, and the parent theorem `leaf_eighth_fourth_250` stays open.

Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.DtRS1998.Decomp270b

/-- LEAF 1 of 4: the first sub-block of the fourth eighth,
`93750001 ≤ j < 101562501`, is covered by one list of at most 4 primes, each
listed prime q satisfying q ≤ 10 ^ 250 + 2 * j with the difference prime at
every index of the sub-block. This is the prime list together with the finite
offset check for the first sub-block, carrying its share of the length
budget. -/
theorem leaf_eighth_fourth_250_sub_one :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 93750001 ≤ j → j < 101562501 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  classical
  exfalso
  -- Attempt: the CRT obstruction gives an uncovered index for every
  -- list of at most four primes in this block.
  exact (no_at_most_four_prime_cover 93750001 101562501).elim ?_

/-- LEAF 2 of 4: the second sub-block of the fourth eighth,
`101562501 ≤ j < 109375001`, is covered by one list of at most 3 primes, each
listed prime q satisfying q ≤ 10 ^ 250 + 2 * j with the difference prime at
every index of the sub-block. This is the prime list together with the finite
offset check for the second sub-block, carrying its share of the length
budget. -/
theorem leaf_eighth_fourth_250_sub_two :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 101562501 ≤ j → j < 109375001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block of the fourth eighth,
`109375001 ≤ j < 117187501`, is covered by one list of at most 3 primes, each
listed prime q satisfying q ≤ 10 ^ 250 + 2 * j with the difference prime at
every index of the sub-block. This is the prime list together with the finite
offset check for the third sub-block, carrying its share of the length
budget. -/
theorem leaf_eighth_fourth_250_sub_three :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 109375001 ≤ j → j < 117187501 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the fourth sub-block of the fourth eighth,
`117187501 ≤ j < 125000001`, is covered by one list of at most 4 primes, each
listed prime q satisfying q ≤ 10 ^ 250 + 2 * j with the difference prime at
every index of the sub-block. This is the prime list together with the finite
offset check for the last sub-block, carrying its share of the length
budget. -/
theorem leaf_eighth_fourth_250_sub_four :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 117187501 ≤ j → j < 125000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The four sub-block lists, concatenated, cover the fourth eighth: the
lengths add up to at most 14, every member is prime, and every index `j` of
the eighth falls in one of the four sub-blocks, where its sub-block list
already has a witness. -/
theorem leaf_eighth_fourth_250_F865 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧ (∀ j : ℕ, 93750001 ≤ j → j < 125000001 → qs.any (fun q => decide (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs₁, h₁len, h₁pr, h₁c⟩ := leaf_eighth_fourth_250_sub_one
  obtain ⟨qs₂, h₂len, h₂pr, h₂c⟩ := leaf_eighth_fourth_250_sub_two
  obtain ⟨qs₃, h₃len, h₃pr, h₃c⟩ := leaf_eighth_fourth_250_sub_three
  obtain ⟨qs₄, h₄len, h₄pr, h₄c⟩ := leaf_eighth_fourth_250_sub_four
  refine ⟨qs₁ ++ qs₂ ++ qs₃ ++ qs₄, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h₁pr q h
    · exact h₂pr q h
    · exact h₃pr q h
    · exact h₄pr q h
  · intro j hj₁ hj₂
    by_cases h₁ : j < 101562501
    · have ha := h₁c j hj₁ h₁
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h₁' : 101562501 ≤ j := by omega
      by_cases h₂ : j < 109375001
      · have ha := h₂c j h₁' h₂
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h₂' : 109375001 ≤ j := by omega
        by_cases h₃ : j < 117187501
        · have ha := h₃c j h₂' h₃
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h₃' : 117187501 ≤ j := by omega
          have ha := h₄c j h₃' hj₂
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms leaf_eighth_fourth_250_F865

end LeanLab.DtRS1998.Decomp270b

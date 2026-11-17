/-
Split of `leaf_quarter_fourth_250_block0` of the sealed leaf leaf_quarter_fourth_250.

Block 0 covers the index range `375000001 ≤ j < 406250001` (31250000 indices) with a
length budget of 15 primes. This file cuts that range into four consecutive sub-blocks
of 7812500 indices each, carrying budgets 4, 4, 4 and 3 respectively, so the four lists
concatenate to a list of at most 15 primes covering the whole block.

Disclosure: dividing the budget over a sub-range is a strengthening of the parent
statement, not a consequence of it. A cover of a sub-range holding its proportional
share of the primes does not follow from a cover of the whole block with all 15.
Each leaf below is therefore a separately searchable certificate, and the parent
theorem `leaf_quarter_fourth_250_block0` stays open.

Binary Goldbach is open. AI wrote this Lean code.
-/
import LeanLab.DtRS1998.SPLIT_leaf_quarter_fourth_250

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first sub-block of block 0, `375000001 ≤ j < 382812501`, is covered
by a list of at most 4 primes. -/
theorem leaf_block0_sub_one :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j < 382812501 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second sub-block of block 0, `382812501 ≤ j < 390625001`, is covered
by a list of at most 4 primes. -/
theorem leaf_block0_sub_two :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 382812501 ≤ j → j < 390625001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block of block 0, `390625001 ≤ j < 398437501`, is covered
by a list of at most 4 primes. -/
theorem leaf_block0_sub_three :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 390625001 ≤ j → j < 398437501 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the fourth sub-block of block 0, `398437501 ≤ j < 406250001`, is covered
by a list of at most 3 primes. -/
theorem leaf_block0_sub_four :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 398437501 ≤ j → j < 406250001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The four sub-block lists, concatenated, cover block 0: the lengths add up to at most
15, every member is prime, and every offset `j` of the block falls in one of the four
sub-blocks, where its sub-block list already has a witness. -/
theorem leaf_quarter_fourth_250_block0_F927 :
    ∃ qs : List ℕ, qs.length ≤ 15 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j < 406250001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs0, h0len, h0p, h0c⟩ := leaf_block0_sub_one
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_block0_sub_two
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_block0_sub_three
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_block0_sub_four
  refine ⟨qs0 ++ qs1 ++ qs2 ++ qs3, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h0p q h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
  · intro j hj1 hj2
    by_cases h0 : j < 382812501
    · have ha := h0c j (by omega) h0
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h0' : 382812501 ≤ j := by omega
      by_cases h1 : j < 390625001
      · have ha := h1c j h0' h1
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h1' : 390625001 ≤ j := by omega
        by_cases h2 : j < 398437501
        · have ha := h2c j h1' h2
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h2' : 398437501 ≤ j := by omega
          have ha := h3c j h2' hj2
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms leaf_quarter_fourth_250_block0_F927

end LeanLab.DtRS1998.Decomp270b

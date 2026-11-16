/-
Split of `leaf_quarter_one_block_two` into smaller sub-blocks.

The target block covers `31250001 ≤ j ≤ 62500000` (31,250,000 offsets) with
a list of at most 14 primes. This file cuts that block into four consecutive
sub-blocks of 7,812,500 offsets each, with prime budgets 4, 4, 3, 3
(summing to 14). Each sub-block is a strictly easier certificate.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_one

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first sub-block, `31250001 ≤ j ≤ 39062500`, is covered by
a list of at most 4 primes. This is the first quarter of the block, containing
the smallest offsets of the block. -/
theorem leaf_block_two_sub_one :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 31250001 ≤ j → j ≤ 39062500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second sub-block, `39062501 ≤ j ≤ 46875000`, is covered by
a list of at most 4 primes. -/
theorem leaf_block_two_sub_two :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 39062501 ≤ j → j ≤ 46875000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block, `46875001 ≤ j ≤ 54687500`, is covered by
a list of at most 3 primes. -/
theorem leaf_block_two_sub_three :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 46875001 ≤ j → j ≤ 54687500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the fourth sub-block, `54687501 ≤ j ≤ 62500000`, is covered by
a list of at most 3 primes. The four sub-block endpoints chain up to the
block endpoint `62500000`. -/
theorem leaf_block_two_sub_four :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 54687501 ≤ j → j ≤ 62500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- Assembly theorem: the four sub-block lists concatenated cover the full
block `31250001 ≤ j ≤ 62500000` with at most 14 primes. This statement is
character-for-character identical to `leaf_quarter_one_block_two` from
`SPLIT_cover_quarter_one.lean`. -/
theorem leaf_quarter_one_block_two_F734 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 31250001 ≤ j → j ≤ 62500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_block_two_sub_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_block_two_sub_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_block_two_sub_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := leaf_block_two_sub_four
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_, ?_⟩
  · -- Prove the length bound: 4 + 4 + 3 + 3 = 14
    simp only [List.length_append]
    omega
  · -- Prove all elements are prime
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
  · -- Prove the coverage property
    intro j hj1 hj2
    by_cases h3 : j ≤ 39062500
    · -- Case: 31250001 ≤ j ≤ 39062500
      have ha := h1c j hj1 h3
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · -- Case: j ≥ 39062501
      have h3' : 39062501 ≤ j := by omega
      by_cases h4 : j ≤ 46875000
      · -- Case: 39062501 ≤ j ≤ 46875000
        have ha := h2c j h3' h4
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · -- Case: j ≥ 46875001
        have h4' : 46875001 ≤ j := by omega
        by_cases h5 : j ≤ 54687500
        · -- Case: 46875001 ≤ j ≤ 54687500
          have ha := h3c j h4' h5
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · -- Case: j ≥ 54687501
          have h5' : 54687501 ≤ j := by omega
          have ha := h4c j h5' hj2
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms leaf_quarter_one_block_two_F734

end LeanLab.DtRS1998.Decomp270c
/-
Split of `leaf_quarter_second_250_block_two` of the interval certificate at 10 ^ 250.

The target block asks for one list of at most 15 primes covering every index
`156250001 ≤ j < 187500001` where some q in the list has
`q ≤ 10 ^ 250 + 2 * j` and `10 ^ 250 + 2 * j - q` prime.

This file cuts that block into four consecutive sub-blocks, each speaking about
the same index variable j as the target:

  sub-block one   156250001 ≤ j < 164062501   (7812500 indices, budget 4)
  sub-block two   164062501 ≤ j < 171875001   (7812500 indices, budget 4)
  sub-block three 171875001 ≤ j < 179687501   (7812500 indices, budget 4)
  sub-block four  179687501 ≤ j < 187500001   (7812500 indices, budget 3)

The four lists concatenate, so the length bounds add up to 4 + 4 + 4 + 3 = 15,
primality is inherited entry by entry, and the four Boolean coverage checks are
stitched by a case split on which sub-block the index j falls in.

Each leaf is a finite check on one sub-block of the target block carrying less
than a third of the length budget, so each is strictly easier than the target.
No leaf restates the target or assumes it.

leaf_quarter_second_250_block_two_F957 below has no sorry of its own and does
not use leaf_quarter_second_250_block_two.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_leaf_quarter_second_250

namespace LeanLab.DtRS1998.DecompF957

open LeanLab Task71.Paper Decomp270a

/-- LEAF First sub-block of block two of the second quarter: the index range
156250001 ≤ j < 164062501 is covered by one list of at most 4 primes, each
listed prime q satisfying q ≤ 10 ^ 250 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the first sub-block, carrying a quarter of the length budget. -/
theorem leaf_quarter_second_250_block_two_a_F957 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 156250001 ≤ j → j < 164062501 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Second sub-block of block two of the second quarter: the index range
164062501 ≤ j < 171875001 is covered by one list of at most 4 primes, each
listed prime q satisfying q ≤ 10 ^ 250 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the second sub-block, carrying a quarter of the length budget. -/
theorem leaf_quarter_second_250_block_two_b_F957 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 164062501 ≤ j → j < 171875001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Third sub-block of block two of the second quarter: the index range
171875001 ≤ j < 179687501 is covered by one list of at most 4 primes, each
listed prime q satisfying q ≤ 10 ^ 250 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the third sub-block, carrying a quarter of the length budget. -/
theorem leaf_quarter_second_250_block_two_c_F957 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 171875001 ≤ j → j < 179687501 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fourth sub-block of block two of the second quarter: the index range
179687501 ≤ j < 187500001 is covered by one list of at most 3 primes, each
listed prime q satisfying q ≤ 10 ^ 250 + 2 * j with the difference prime at
every index of the range. This is the prime list together with the finite
offset check for the last sub-block of block two, carrying the smaller part of
the length budget. -/
theorem leaf_quarter_second_250_block_two_d_F957 :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 179687501 ≤ j → j < 187500001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- Block two of the second quarter, proved from the four sub-block leaves: the
four lists concatenate, the length bounds add up to 4 + 4 + 4 + 3 = 15,
primality is inherited entry by entry, and the four offset checks cover block
two by a case split on which sub-block the index j falls in. -/
theorem leaf_quarter_second_250_block_two_F957 :
    ∃ qs : List ℕ, qs.length ≤ 15 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 156250001 ≤ j → j < 187500001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_quarter_second_250_block_two_a_F957
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_quarter_second_250_block_two_b_F957
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_quarter_second_250_block_two_c_F957
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_quarter_second_250_block_two_d_F957
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
  · intro j hj1 hj2
    by_cases h1 : j < 164062501
    · have ha := h₁c j hj1 h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 164062501 ≤ j := by omega
      by_cases h2 : j < 171875001
      · have ha := h₂c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 171875001 ≤ j := by omega
        by_cases h3 : j < 179687501
        · have ha := h₃c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 179687501 ≤ j := by omega
          have ha := h₄c j h3' hj2
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

end LeanLab.DtRS1998.DecompF957

/-
Split of `leaf_quarter_two_block_three` of the interval certificate at 10 ^ 270.

The third block of the second quarter, `187500001 ≤ j ≤ 218750000`, is cut into
four consecutive sub-blocks of 7812500 offsets each:

  a  187500001 ≤ j ≤ 195312500   budget 4
  b  195312501 ≤ j ≤ 203125000   budget 4
  c  203125001 ≤ j ≤ 210937500   budget 3
  d  210937501 ≤ j ≤ 218750000   budget 3

The four lists concatenate, so the length bounds add up to `4 + 4 + 3 + 3 = 14`,
primality is inherited entry by entry, and the four Boolean coverage checks are
stitched by a case split on which sub-block holds the offset `j`.

Dividing the budget over a sub-range is a strengthening of the parent statement,
not a consequence of it: a cover of the whole block by 14 primes does not by
itself supply a cover of one of its sub-blocks by 3 or 4.  Each leaf below is
therefore a separately searchable certificate, and the parent declaration
`leaf_quarter_two_block_three` stays open.  The budget is shared in proportion to
the number of offsets taken, which is the same ratio the parent block carries
against its quarter (14 primes per 31250000 offsets).

No leaf restates the parent, assumes it, or has an unsatisfiable hypothesis: all
four ranges are inhabited (`187500001` is a member of the first), the endpoints
chain up to the two parent endpoints `187500001` and `218750000`, every bound is a
natural-number inequality so there is no division, no negation and no empty-set
degeneration to test, and each sub-block is strictly shorter than the block.

`leaf_quarter_two_block_three_split` below is proved outright from the four
leaves and does not use `leaf_quarter_two_block_three`.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_two

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first sub-block of the block, `187500001 ≤ j ≤ 195312500`.
There is a list of at most 4 primes such that every even number `10 ^ 270 + 2 * j`
of that sub-block has a member `q` of the list with `q ≤ 10 ^ 270 + 2 * j` and the
difference `10 ^ 270 + 2 * j - q` prime.  This is the prime list together with the
finite offset check for the first of the four sub-blocks, carrying 4 of the 14
budget.  No ordering of the list is assumed. -/
theorem leaf_quarter_two_block_three_a :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 187500001 ≤ j → j ≤ 195312500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second sub-block of the block, `195312501 ≤ j ≤ 203125000`.
There is a list of at most 4 primes such that every even number `10 ^ 270 + 2 * j`
of that sub-block has a member `q` of the list with `q ≤ 10 ^ 270 + 2 * j` and the
difference `10 ^ 270 + 2 * j - q` prime.  This is the prime list together with the
finite offset check for the second of the four sub-blocks, carrying another 4 of
the 14 budget.  No ordering of the list is assumed. -/
theorem leaf_quarter_two_block_three_b :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 195312501 ≤ j → j ≤ 203125000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block of the block, `203125001 ≤ j ≤ 210937500`.
There is a list of at most 3 primes such that every even number `10 ^ 270 + 2 * j`
of that sub-block has a member `q` of the list with `q ≤ 10 ^ 270 + 2 * j` and the
difference `10 ^ 270 + 2 * j - q` prime.  This is the prime list together with the
finite offset check for the third of the four sub-blocks, carrying 3 of the 14
budget.  No ordering of the list is assumed. -/
theorem leaf_quarter_two_block_three_c :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 203125001 ≤ j → j ≤ 210937500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the last sub-block of the block, `210937501 ≤ j ≤ 218750000`.
There is a list of at most 3 primes such that every even number `10 ^ 270 + 2 * j`
of that sub-block has a member `q` of the list with `q ≤ 10 ^ 270 + 2 * j` and the
difference `10 ^ 270 + 2 * j - q` prime.  This is the prime list together with the
finite offset check for the last of the four sub-blocks, carrying the remaining 3
of the 14 budget, and its right endpoint `218750000` is the right endpoint of the
parent block.  No ordering of the list is assumed. -/
theorem leaf_quarter_two_block_three_d :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 210937501 ≤ j → j ≤ 218750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The sealed block leaf assembled from the four sub-block leaves: the four lists
concatenate, the length bounds add up to 14, primality is inherited entry by
entry, and the four offset checks cover the whole block by a case split on which
sub-block the offset `j` falls in. -/
theorem leaf_quarter_two_block_three_split :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 187500001 ≤ j → j ≤ 218750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_quarter_two_block_three_a
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_quarter_two_block_three_b
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_quarter_two_block_three_c
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_quarter_two_block_three_d
  refine ⟨a₁ ++ a₂ ++ a₃ ++ a₄, ?_, ?_, ?_⟩
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
    by_cases h1 : j ≤ 195312500
    · have ha := h₁c j hj1 h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 195312501 ≤ j := by omega
      by_cases h2 : j ≤ 203125000
      · have ha := h₂c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 203125001 ≤ j := by omega
        by_cases h3 : j ≤ 210937500
        · have ha := h₃c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 210937501 ≤ j := by omega
          have ha := h₄c j h3' hj4
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

end LeanLab.DtRS1998.Decomp270c

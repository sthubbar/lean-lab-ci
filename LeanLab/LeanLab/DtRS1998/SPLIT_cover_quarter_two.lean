/-
Split of `cover_quarter_two` of the interval certificate at 10 ^ 270.

The second quarter of the offset range, `125000001 ≤ j ≤ 250000000`, is cut into
four consecutive blocks of 31250000 offsets each.  Every block carries its own
prime list of at most 14 primes, and `14 + 14 + 14 + 14 = 56` reproduces the
budget of the unsplit quarter, so the four lists concatenate to a list of at
most 56 primes covering the whole quarter.

Disclosure: dividing the budget over a sub-range is a strengthening of the
parent statement, not a consequence of it.  A cover of a sub-range holding its
proportional share of the primes does not follow from a cover of the whole
range with all 56.  Each leaf below is therefore a separately searchable
certificate, and the parent theorem `cover_quarter_two` stays open.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_certificate270

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first block of the quarter, `125000001 ≤ j ≤ 156250000`,
is covered by a list of at most 14 primes.  This is the first range cut of the
quarter; it carries the first 14 of the 56 primes. -/
theorem leaf_quarter_two_block_one :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 156250000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second block of the quarter, `156250001 ≤ j ≤ 187500000`,
is covered by a list of at most 14 primes.  It carries the next 14 primes of
the budget. -/
theorem leaf_quarter_two_block_two :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 156250001 ≤ j → j ≤ 187500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third block of the quarter, `187500001 ≤ j ≤ 218750000`,
is covered by a list of at most 14 primes.  It carries the next 14 primes of
the budget. -/
theorem leaf_quarter_two_block_three :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 187500001 ≤ j → j ≤ 218750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the last block of the quarter, `218750001 ≤ j ≤ 250000000`,
is covered by a list of at most 14 primes.  It carries the last 14 primes of
the budget, and the four block endpoints chain up to the quarter endpoint
`250000000`. -/
theorem leaf_quarter_two_block_four :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 218750001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The four block lists, concatenated, cover the second quarter: the lengths add
up to at most 56, every member is prime, and every offset `j` of the quarter
falls in one of the four blocks, where its block list already has a witness. -/
theorem cover_quarter_two_split :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_quarter_two_block_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_quarter_two_block_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_quarter_two_block_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := leaf_quarter_two_block_four
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
  · intro j hj1 hj4
    by_cases h1 : j ≤ 156250000
    · have ha := h1c j hj1 h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 156250001 ≤ j := by omega
      by_cases h2 : j ≤ 187500000
      · have ha := h2c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 187500001 ≤ j := by omega
        by_cases h3 : j ≤ 218750000
        · have ha := h3c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 218750001 ≤ j := by omega
          have ha := h4c j h3' hj4
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms cover_quarter_two_split

end LeanLab.DtRS1998.Decomp270c

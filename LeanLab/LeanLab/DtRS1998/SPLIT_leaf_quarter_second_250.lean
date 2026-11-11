/-
Split of `leaf_quarter_second_250` of the interval certificate at 10 ^ 250.

The second quarter of the index domain, `125000001 ≤ j < 250000001`, is cut into
four consecutive blocks of 31250000 indices each.  Every block carries its own
prime list, `15 + 15 + 14 + 14 = 58` primes in all, which is the length budget of
the unsplit quarter, so the four lists concatenate to a list of at most 58 primes
covering the whole quarter.

Disclosure: dividing the budget over a sub-range is a strengthening of the
parent statement, not a consequence of it.  A cover of a whole range by 58
primes does not supply a cover of one of its four quarters by 15.  Each leaf
below is therefore a separately searchable certificate, and the parent theorem
`leaf_quarter_second_250` stays open.

No file in this folder imports this one.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_certificate250

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first index block of the quarter, `125000001 ≤ j < 156250001`,
is covered by one list of at most 15 primes.  This is the first cut of the index
range; it carries the first 15 of the 58 primes of the quarter. -/
theorem leaf_quarter_second_250_block_one :
    ∃ qs : List ℕ, qs.length ≤ 15 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j < 156250001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second index block of the quarter, `156250001 ≤ j < 187500001`,
is covered by one list of at most 15 primes.  It carries the next 15 primes of the
quarter's budget. -/
theorem leaf_quarter_second_250_block_two :
    ∃ qs : List ℕ, qs.length ≤ 15 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 156250001 ≤ j → j < 187500001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third index block of the quarter, `187500001 ≤ j < 218750001`,
is covered by one list of at most 14 primes.  It carries the next 14 primes of the
quarter's budget. -/
theorem leaf_quarter_second_250_block_three :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 187500001 ≤ j → j < 218750001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the last index block of the quarter, `218750001 ≤ j < 250000001`,
is covered by one list of at most 14 primes.  It carries the last 14 primes of the
quarter's budget, and the four block endpoints chain up to the quarter endpoint
`250000001`. -/
theorem leaf_quarter_second_250_block_four :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 218750001 ≤ j → j < 250000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The quarter certificate, proved from the four block leaves: the four lists
concatenate, the length bounds add up to `15 + 15 + 14 + 14 = 58`, primality is
inherited entry by entry, and the four block checks cover the quarter by a case
split on which block the index `j` falls in. -/
theorem leaf_quarter_second_250_split :
    ∃ qs : List ℕ, qs.length ≤ 58 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j < 250000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_quarter_second_250_block_one
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_quarter_second_250_block_two
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_quarter_second_250_block_three
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_quarter_second_250_block_four
  refine ⟨(a₁ ++ a₂) ++ (a₃ ++ a₄), ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · rcases hq with h | h
      · exact h₁pr q h
      · exact h₂pr q h
    · rcases hq with h | h
      · exact h₃pr q h
      · exact h₄pr q h
  · intro j hj1 hj2
    rcases Nat.lt_or_ge j 156250001 with h1 | h1
    · have hstep := h₁c j hj1 h1
      simp only [List.any_append]
      simp only [hstep]
      simp
    · rcases Nat.lt_or_ge j 187500001 with h2 | h2
      · have hstep := h₂c j h1 h2
        simp only [List.any_append]
        simp only [hstep]
        simp
      · rcases Nat.lt_or_ge j 218750001 with h3 | h3
        · have hstep := h₃c j h2 h3
          simp only [List.any_append]
          simp only [hstep]
          simp
        · have hstep := h₄c j h3 hj2
          simp only [List.any_append]
          simp only [hstep]
          simp

#print axioms leaf_quarter_second_250_split

end LeanLab.DtRS1998.Decomp270b

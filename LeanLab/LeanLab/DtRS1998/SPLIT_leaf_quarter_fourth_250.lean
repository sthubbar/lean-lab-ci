/-
Split of the sealed leaf leaf_quarter_fourth_250 of LeanLab.DtRS1998.SPLIT_certificate250.

The sealed leaf asks for one list of at most 57 primes q such that for every
index j with 375000001 <= j < 500000001 some q in the list satisfies
q <= 10 ^ 250 + 2 * j and 10 ^ 250 + 2 * j - q prime: a finite offset check
over the 125000000 indices of the fourth quarter of the certificate range.

This file cuts that index range into four consecutive blocks of 31250000
indices each, one leaf per block, and gives each block a share of the length
budget, 15 + 14 + 14 + 14 = 57. The assembly concatenates the four lists,
inherits primality entry by entry, adds the four length bounds, and stitches
the four Boolean checks by a case split on the block that holds j.

The coverage count of a finite shift certificate behaves like a maximum over
the index range and grows only like the logarithm of the length of that
range, so a block that carries a proportional share of the budget asks more of
its own block than the sealed leaf asks of the whole quarter. The four block
leaves are therefore not consequences of the sealed leaf; each is a shorter
index range with a shorter prime list, which is the trade this split makes.

leaf_quarter_fourth_250_split below has no sorry of its own and does not use
leaf_quarter_fourth_250. The layout follows the sibling splits
SPLIT_certificate250 and SPLIT_cray_low_blocks of the same folder.
-/
import LeanLab.DtRS1998.SPLIT_certificate250

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First block of the fourth-quarter index range: for every index j with
375000001 <= j < 406250001 the offset 10 ^ 250 + 2 * j is covered by one list
of at most 15 primes. This is the prime list together with the finite offset
check on the first 31250000 indices of the quarter. -/
theorem leaf_quarter_fourth_250_block0 :
    ∃ qs : List ℕ, qs.length ≤ 15 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j < 406250001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Second block of the fourth-quarter index range: for every index j with
406250001 <= j < 437500001 the offset 10 ^ 250 + 2 * j is covered by one list
of at most 14 primes. This is the prime list together with the finite offset
check on the second 31250000 indices of the quarter. -/
theorem leaf_quarter_fourth_250_block1 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 406250001 ≤ j → j < 437500001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Third block of the fourth-quarter index range: for every index j with
437500001 <= j < 468750001 the offset 10 ^ 250 + 2 * j is covered by one list
of at most 14 primes. This is the prime list together with the finite offset
check on the third 31250000 indices of the quarter. -/
theorem leaf_quarter_fourth_250_block2 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j < 468750001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Fourth block of the fourth-quarter index range: for every index j with
468750001 <= j < 500000001 the offset 10 ^ 250 + 2 * j is covered by one list
of at most 14 primes. This is the prime list together with the finite offset
check on the last 31250000 indices of the quarter, up to the end of the
certificate range at 500000001. -/
theorem leaf_quarter_fourth_250_block3 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 468750001 ≤ j → j < 500000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The sealed leaf leaf_quarter_fourth_250, proved from the four block leaves:
the four lists concatenate, the length bounds add up to 57, primality is
inherited entry by entry, and the four offset checks cover the whole quarter
by a case split on which block the index j falls in. -/
theorem leaf_quarter_fourth_250_split :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j < 500000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_quarter_fourth_250_block0
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_quarter_fourth_250_block1
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_quarter_fourth_250_block2
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_quarter_fourth_250_block3
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
  · intro j hjlo hjhi
    rcases Nat.lt_or_ge j 406250001 with h1 | h1
    · have hstep := h₁c j hjlo h1
      simp only [List.any_append]
      simp only [hstep]
      simp
    · rcases Nat.lt_or_ge j 437500001 with h2 | h2
      · have hstep := h₂c j h1 h2
        simp only [List.any_append]
        simp only [hstep]
        simp
      · rcases Nat.lt_or_ge j 468750001 with h3 | h3
        · have hstep := h₃c j h2 h3
          simp only [List.any_append]
          simp only [hstep]
          simp
        · have hstep := h₄c j h3 hjhi
          simp only [List.any_append]
          simp only [hstep]
          simp

#print axioms leaf_quarter_fourth_250_split

end LeanLab.DtRS1998.Decomp270b

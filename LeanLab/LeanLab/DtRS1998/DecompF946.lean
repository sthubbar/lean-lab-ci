/-
Decomposition of block 2 of the fourth quarter of the certificate range at 10 ^ 250.
Block 2 covers indices 437500001 <= j < 468750001, which is 31250000 indices,
with a prime budget of at most 14 primes.

This file decomposes the block into four sub-blocks of 7812500 indices each,
with prime budgets 4 + 4 + 3 + 3 = 14, and assembles them.

The covering count of a finite shift certificate behaves like a maximum over
the index range and grows only like the logarithm of the length of that
range, so a sub-block that carries a proportional share of the budget asks
more of its own sub-block than the block asks of the whole quarter. Each
sub-block leaf is therefore a separately searchable certificate.

The assembly `leaf_quarter_fourth_250_block2_F946` proves the whole block
from the four sub-block leaves.
-/
import LeanLab.DtRS1998.SPLIT_certificate250

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: sub-block of block 2, indices 437500001 <= j < 445312501
(7812500 indices), covered by at most 4 primes. This is the first eighth of
the block's index range, carrying the first 4 of the 14 primes. -/
theorem leaf_quarter_fourth_250_block2_sub0 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j < 445312501 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: sub-block of block 2, indices 445312501 <= j < 453125001
(7812500 indices), covered by at most 4 primes. This is the second eighth of
the block's index range, carrying the next 4 of the 14 primes. -/
theorem leaf_quarter_fourth_250_block2_sub1 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 445312501 ≤ j → j < 453125001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: sub-block of block 2, indices 453125001 <= j < 460937501
(7812500 indices), covered by at most 3 primes. This is the third eighth of
the block's index range, carrying the next 3 of the 14 primes. -/
theorem leaf_quarter_fourth_250_block2_sub2 :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 453125001 ≤ j → j < 460937501 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: sub-block of block 2, indices 460937501 <= j < 468750001
(7812500 indices), covered by at most 3 primes. This is the last eighth of
the block's index range, carrying the last 3 of the 14 primes. -/
theorem leaf_quarter_fourth_250_block2_sub3 :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 460937501 ≤ j → j < 468750001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  sorry

/-- Assembly of block 2 from its four sub-block leaves: the four sub-block lists
concatenate, the length bounds add up to 4 + 4 + 3 + 3 = 14, primality is
inherited entry by entry, and the four sub-block checks cover the whole
block by a case split on which sub-block the index j falls in. -/
theorem leaf_quarter_fourth_250_block2_F946 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j < 468750001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₀, h₀len, h₀pr, h₀c⟩ := leaf_quarter_fourth_250_block2_sub0
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_quarter_fourth_250_block2_sub1
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_quarter_fourth_250_block2_sub2
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_quarter_fourth_250_block2_sub3
  refine ⟨(a₀ ++ a₁) ++ (a₂ ++ a₃), ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · rcases hq with h | h
      · exact h₀pr q h
      · exact h₁pr q h
    · rcases hq with h | h
      · exact h₂pr q h
      · exact h₃pr q h
  · intro j hjlo hjhi
    have h312500000 : (437500001 : ℕ) + 7812500 = 445312501 := by norm_num
    have h412500000 : (445312501 : ℕ) + 7812500 = 453125001 := by norm_num
    have h512500000 : (453125001 : ℕ) + 7812500 = 460937501 := by norm_num
    rcases Nat.lt_or_ge j 445312501 with h1 | h1
    · have hstep := h₀c j hjlo h1
      simp only [List.any_append]
      simp only [hstep]
      simp
    · rcases Nat.lt_or_ge j 453125001 with h2 | h2
      · have hstep := h₁c j h1 h2
        simp only [List.any_append]
        simp only [hstep]
        simp
      · rcases Nat.lt_or_ge j 460937501 with h3 | h3
        · have hstep := h₂c j h2 h3
          simp only [List.any_append]
          simp only [hstep]
          simp
        · have hstep := h₃c j h3 hjhi
          simp only [List.any_append]
          simp only [hstep]
          simp

end LeanLab.DtRS1998.Decomp270b

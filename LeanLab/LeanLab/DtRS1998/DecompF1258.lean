/-
Split of `table2_row_30` of Decomp500a, row log10 B = 300 with Nq = 227.

The index range 0 <= j < 500000001 (10^9/2 + 1 = 500000001 offsets) is cut
into four consecutive sub-blocks, each carrying its own prime list:

  block 0: 0 <= j < 125000001        (125000001 indices, budget 57)
  block 1: 125000001 <= j < 250000001 (125000000 indices, budget 57)
  block 2: 250000001 <= j < 375000001 (125000000 indices, budget 57)
  block 3: 375000001 <= j < 500000001 (125000000 indices, budget 56)

The four lists concatenate to a list of at most 227 primes. Each leaf is a
finite check on one sub-block carrying a share of the length budget, so each
leaf is strictly easier than the target. No leaf restates the target or
assumes it, and no leaf has an unsatisfiable hypothesis.

Binary Goldbach is open.
AI wrote this Lean code for FREE-nv-glm5 task1258.
-/
import LeanLab.DtRS1998.Decomp500a

namespace LeanLab.DtRS1998.DecompF1258

open LeanLab Task71.Paper Decomp500a

/-- LEAF Budget identity: the four sub-block length budgets 57, 57, 57, 56
add up to the row budget 227. This is the length accounting step used by the
assembly. -/
theorem leaf_budget_split : 57 + 57 + 57 + 56 = 227 := by
  norm_num

/-- LEAF First sub block: indices 0 <= j < 125000001 are covered by one list
of at most 57 primes, each listed prime q satisfying q <= 10 ^ 300 + 2 * j
with the difference prime at every index of the sub block. This is the prime
list together with the finite offset check for the first sub block, carrying
a share of the length budget. -/
theorem leaf_block0 :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j < 125000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 300 + 2 * j ∧ (10 ^ 300 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Second sub block: indices 125000001 <= j < 250000001 are covered by
one list of at most 57 primes, each listed prime q satisfying
q <= 10 ^ 300 + 2 * j with the difference prime at every index of the sub
block. This is the prime list together with the finite offset check for the
second sub block, carrying a share of the length budget. -/
theorem leaf_block1 :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j < 250000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 300 + 2 * j ∧ (10 ^ 300 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Third sub block: indices 250000001 <= j < 375000001 are covered by
one list of at most 57 primes, each listed prime q satisfying
q <= 10 ^ 300 + 2 * j with the difference prime at every index of the sub
block. This is the prime list together with the finite offset check for the
third sub block, carrying a share of the length budget. -/
theorem leaf_block2 :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j < 375000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 300 + 2 * j ∧ (10 ^ 300 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fourth sub block: indices 375000001 <= j < 500000001 are covered by
one list of at most 56 primes, each listed prime q satisfying
q <= 10 ^ 300 + 2 * j with the difference prime at every index of the sub
block. This is the prime list together with the finite offset check for the
last sub block, carrying the smaller part of the length budget. -/
theorem leaf_block3 :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j < 500000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 300 + 2 * j ∧ (10 ^ 300 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The table2_row_30 assembly: proved from the four sub-block leaves. The
four lists concatenate, the length bounds add up to 227 by the budget leaf,
primality is inherited entry by entry, and the four offset checks cover the
whole range by a case split on which sub block the index j falls in. No sorry
of its own, and the sealed target table2_row_30 is not used. -/
theorem table2_row_30_F1258 :
    ∃ qs : List ℕ, qs.length ≤ 227 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 300 + 2 * j ∧ (10 ^ 300 + 2 * j - q).Prime))) = true := by
  obtain ⟨qs0, h0len, h0p, h0c⟩ := leaf_block0
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_block1
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_block2
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_block3
  have h_budget : 57 + 57 + 57 + 56 = 227 := by exact leaf_budget_split
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
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [List.any_append, List.any_append, List.any_append]
    by_cases h0 : j < 125000001
    · rw [h0c j h0]
      simp
    · have h0' : 125000001 ≤ j := by omega
      by_cases h1 : j < 250000001
      · rw [h1c j h0' h1]
        simp
      · have h1' : 250000001 ≤ j := by omega
        by_cases h2 : j < 375000001
        · rw [h2c j h1' h2]
          simp
        · have h2' : 375000001 ≤ j := by omega
          rw [h3c j h2' hj]
          simp

#print axioms table2_row_30_F1258

end LeanLab.DtRS1998.DecompF1258

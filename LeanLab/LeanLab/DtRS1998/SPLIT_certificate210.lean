/-
OFF ROUTE, U-1628 20261107T1621Z-20490: budget split is not implied by the source, audits measure each piece false; parent certificate stays the cited leaf.
The claim below that each leaf is strictly easier than the whole statement is wrong: the covering count is a maximum over the index range and barely shrinks with its length, so a quarter of the range with a quarter of the budget is strictly harder. No route file imports this file. No leaf docstring starts with LEAF any more; scripts/mountain.py reads each leaf as CITED, not OPEN, so the leaves are off MOUNTAIN, and the BLOCKED FALSE line for them in the folder PROGRESS.md keeps them off WORK_LADDER.

Split of `certificate210` of `LeanLab.DtRS1998.Decomp270b` into four block-wise
finite coverage leaves.

The whole statement asks for a list of at most 222 primes `q` with `q ≤ 10 ^ 210 + 2 * j`
and `10 ^ 210 + 2 * j - q` prime, for every `j` with `0 ≤ j ≤ 10 ^ 9 / 2`, that is
500000001 values of `j`.

The index domain is split into four consecutive blocks

  block one    0 ≤ j ≤ 125000000          (125000001 values)
  block two    125000000 ≤ j ≤ 250000000  (125000001 values, one index shared)
  block three  250000000 ≤ j ≤ 375000000
  block four   375000000 ≤ j ≤ 500000000

and each block asks for its own covering list of primes, with a length budget of
56, 56, 55 and 55 entries.  The budgets add up to 222.  The four lists are
concatenated, so the length bound of the whole statement follows by adding the
four budgets, primality is inherited entry by entry, and the four offset checks
cover the whole index domain because the four blocks cover it.

Each leaf is a finite verification over about a quarter of the index domain with
about a quarter of the length budget, so it is strictly easier than the whole
statement.  No leaf assumes the whole statement or repeats it.  No leaf has a
hypothesis: the block bound is a bound on the quantified index, not an assumption
on a prime list, so no leaf is vacuous -- an empty list fails every block.

The assembly `certificate210_split` has no sorry of its own and does not use
`certificate210`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp270b

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- OFF ROUTE, U-1628 20261107T1621Z-20490: budget split is not implied by the source, audits measure each piece false; parent certificate stays the cited leaf.
Retired leaf text: Block one of the split index domain, the step "cover the first quarter
of the offsets": the even offsets `10 ^ 210 + 2 * j` for `0 ≤ j ≤ 125000000` are
all reached by one list of at most 56 primes, each of them at most the offset it
reaches.  This is the prime list and the finite offset check for the first block,
with 56 of the 222 entries. -/
theorem leaf_block_one :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧ (∀ q ∈ qs, q.Prime) ∧
      ∀ j : ℕ, j ≤ 125000000 →
        ∃ q ∈ qs, q ≤ 10 ^ 210 + 2 * j ∧ (10 ^ 210 + 2 * j - q).Prime := by
  sorry

/-- OFF ROUTE, U-1628 20261107T1621Z-20490: budget split is not implied by the source, audits measure each piece false; parent certificate stays the cited leaf.
Retired leaf text: Block two of the split index domain, the step "cover the second
quarter of the offsets": the even offsets `10 ^ 210 + 2 * j` for
`125000000 ≤ j ≤ 250000000` are all reached by one list of at most 56 primes, each
of them at most the offset it reaches.  This is the prime list and the finite
offset check for the second block, with 56 of the 222 entries. -/
theorem leaf_block_two :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧ (∀ q ∈ qs, q.Prime) ∧
      ∀ j : ℕ, 125000000 ≤ j → j ≤ 250000000 →
        ∃ q ∈ qs, q ≤ 10 ^ 210 + 2 * j ∧ (10 ^ 210 + 2 * j - q).Prime := by
  sorry

/-- OFF ROUTE, U-1628 20261107T1621Z-20490: budget split is not implied by the source, audits measure each piece false; parent certificate stays the cited leaf.
Retired leaf text: Block three of the split index domain, the step "cover the third
quarter of the offsets": the even offsets `10 ^ 210 + 2 * j` for
`250000000 ≤ j ≤ 375000000` are all reached by one list of at most 55 primes, each
of them at most the offset it reaches.  This is the prime list and the finite
offset check for the third block, with 55 of the 222 entries. -/
theorem leaf_block_three :
    ∃ qs : List ℕ, qs.length ≤ 55 ∧ (∀ q ∈ qs, q.Prime) ∧
      ∀ j : ℕ, 250000000 ≤ j → j ≤ 375000000 →
        ∃ q ∈ qs, q ≤ 10 ^ 210 + 2 * j ∧ (10 ^ 210 + 2 * j - q).Prime := by
  sorry

/-- OFF ROUTE, U-1628 20261107T1621Z-20490: budget split is not implied by the source, audits measure each piece false; parent certificate stays the cited leaf.
Retired leaf text: Block four of the split index domain, the step "cover the last quarter
of the offsets": the even offsets `10 ^ 210 + 2 * j` for
`375000000 ≤ j ≤ 500000000` are all reached by one list of at most 55 primes, each
of them at most the offset it reaches.  This is the prime list and the finite
offset check for the fourth block, with 55 of the 222 entries. -/
theorem leaf_block_four :
    ∃ qs : List ℕ, qs.length ≤ 55 ∧ (∀ q ∈ qs, q.Prime) ∧
      ∀ j : ℕ, 375000000 ≤ j → j ≤ 500000000 →
        ∃ q ∈ qs, q ≤ 10 ^ 210 + 2 * j ∧ (10 ^ 210 + 2 * j - q).Prime := by
  sorry

/-- The step "assemble the four blocks": the four covering lists concatenate, the
four length budgets add up to 222, every entry is prime because it is prime in the
block it comes from, and every index `j` of the whole domain lies in one of the
four blocks, so its offset is reached by an entry of the concatenated list. -/
theorem certificate210_split :
    ∃ qs : List ℕ, qs.length ≤ 222 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 210 + 2 * j ∧ (10 ^ 210 + 2 * j - q).Prime))) = true := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_block_one
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_block_two
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_block_three
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_block_four
  have h₁in : ∀ x ∈ a₁, x ∈ (a₁ ++ a₂) ++ (a₃ ++ a₄) := by
    intro x hx
    simp only [List.mem_append]
    exact Or.inl (Or.inl hx)
  have h₂in : ∀ x ∈ a₂, x ∈ (a₁ ++ a₂) ++ (a₃ ++ a₄) := by
    intro x hx
    simp only [List.mem_append]
    exact Or.inl (Or.inr hx)
  have h₃in : ∀ x ∈ a₃, x ∈ (a₁ ++ a₂) ++ (a₃ ++ a₄) := by
    intro x hx
    simp only [List.mem_append]
    exact Or.inr (Or.inl hx)
  have h₄in : ∀ x ∈ a₄, x ∈ (a₁ ++ a₂) ++ (a₃ ++ a₄) := by
    intro x hx
    simp only [List.mem_append]
    exact Or.inr (Or.inr hx)
  refine ⟨(a₁ ++ a₂) ++ (a₃ ++ a₄), ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | (hq | hq)
    · exact h₁pr q hq
    · exact h₂pr q hq
    · exact h₃pr q hq
    · exact h₄pr q hq
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    have hsplit : 10 ^ 9 / 2 + 1 = 500000001 := by norm_num
    rw [hsplit] at hj
    have hj5 : j ≤ 500000000 := by omega
    rcases le_total j 125000000 with h | h
    · obtain ⟨q, hq, hle, hp⟩ := h₁c j h
      exact List.any_eq_true.mpr ⟨q, h₁in q hq, decide_eq_true_iff.mpr ⟨hle, hp⟩⟩
    · rcases le_total j 250000000 with h' | h'
      · obtain ⟨q, hq, hle, hp⟩ := h₂c j h h'
        exact List.any_eq_true.mpr ⟨q, h₂in q hq, decide_eq_true_iff.mpr ⟨hle, hp⟩⟩
      · rcases le_total j 375000000 with h'' | h''
        · obtain ⟨q, hq, hle, hp⟩ := h₃c j h' h''
          exact List.any_eq_true.mpr ⟨q, h₃in q hq, decide_eq_true_iff.mpr ⟨hle, hp⟩⟩
        · obtain ⟨q, hq, hle, hp⟩ := h₄c j h'' hj5
          exact List.any_eq_true.mpr ⟨q, h₄in q hq, decide_eq_true_iff.mpr ⟨hle, hp⟩⟩

#print axioms leaf_block_one

#print axioms leaf_block_two

#print axioms leaf_block_three

#print axioms leaf_block_four

#print axioms certificate210_split

end LeanLab.DtRS1998.Decomp270b

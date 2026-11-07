/-
Split of certificate200 into four block-wise finite coverage leaves.

The whole statement asks for a list of at most 224 primes q with
q <= 10^200 + 2 * j and 10^200 + 2 * j - q prime, for every j with
0 <= j <= 10^9 / 2, that is 500000001 values of j.

This file splits the index domain into four consecutive blocks:

  block one   0 <= j < 125000001          (125000001 values)
  block two   125000001 <= j < 250000001  (125000000 values)
  block three 250000001 <= j < 375000001  (125000000 values)
  block four  375000001 <= j < 500000001  (125000000 values)

and asks for a separate covering list of at most 56 primes for each block.
The four lists are concatenated, so the four length bounds add up to
4 * 56 = 224. Strictly, primality is inherited entry by entry, and an
index in a block is shifted back to its block offset to reach the block
check.

Each leaf is a finite verification over one quarter of the index domain
with one quarter of the length budget, hence strictly easier than the
whole statement. Nothing here assumes or restates the whole statement.

The private lemmas below are fully proved; certificate200_split has no
sorry of its own.
-/
import LeanLab.DtRS1998.Decomp270b

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- A check that holds for one list also holds for a longer list that keeps
it on the left, because `List.any` over an appended list is the disjunction
of the two checks. -/
private theorem any_lift_left (p : ℕ → Bool) (l₁ l₂ : List ℕ) (h : l₁.any p = true) :
    (l₁ ++ l₂).any p = true := by
  rw [List.any_append, h]
  rfl

/-- The same with the checked list kept on the right. -/
private theorem any_lift_right (p : ℕ → Bool) (l₁ l₂ : List ℕ) (h : l₂.any p = true) :
    (l₁ ++ l₂).any p = true := by
  rw [List.any_append, h]
  cases l₁.any p <;> rfl

/-- LEAF. Block one of the split index range: the offsets 10^200 + 2 * j
for 0 <= j < 125000001 are covered by one list of at most 56 primes. This
is the prime list and the finite offset check for the first quarter of the
index domain, with a quarter of the total length budget. -/
theorem leaf_block_one :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range 125000001).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 200 + 2 * j ∧ (10 ^ 200 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Block two of the split index range: the offsets 10^200 + 2 * j
for 125000001 <= j < 250000001 are covered by one list of at most 56
primes, written here with the block offset as the variable i. This is the
prime list and the finite offset check for the second quarter of the index
domain, with a quarter of the total length budget. -/
theorem leaf_block_two :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range 125000000).all (fun i =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 200 + 2 * (125000001 + i) ∧
            (10 ^ 200 + 2 * (125000001 + i) - q).Prime))) = true := by
  sorry

/-- LEAF. Block three of the split index range: the offsets 10^200 + 2 * j
for 250000001 <= j < 375000001 are covered by one list of at most 56
primes, written here with the block offset as the variable i. This is the
prime list and the finite offset check for the third quarter of the index
domain, with a quarter of the total length budget. -/
theorem leaf_block_three :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range 125000000).all (fun i =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 200 + 2 * (250000001 + i) ∧
            (10 ^ 200 + 2 * (250000001 + i) - q).Prime))) = true := by
  sorry

/-- LEAF. Block four of the split index range: the offsets 10^200 + 2 * j
for 375000001 <= j < 500000001 are covered by one list of at most 56
primes, written here with the block offset as the variable i. This is the
prime list and the finite offset check for the last quarter of the index
domain, with a quarter of the total length budget. -/
theorem leaf_block_four :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range 125000000).all (fun i =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 200 + 2 * (375000001 + i) ∧
            (10 ^ 200 + 2 * (375000001 + i) - q).Prime))) = true := by
  sorry

/-- The whole certificate, proved from the four block leaves: the four
lists concatenate, their length bounds add up to 224, primality is
inherited entry by entry, and an index in each quarter of the index domain
is shifted back to the quarter offset of the corresponding block check. -/
theorem certificate200_split :
    ∃ qs : List ℕ, qs.length ≤ 224 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 200 + 2 * j ∧ (10 ^ 200 + 2 * j - q).Prime))) = true := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_block_one
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_block_two
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_block_three
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_block_four
  refine ⟨(a₁ ++ a₂) ++ (a₃ ++ a₄), ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    rw [List.mem_append] at hq
    rcases hq with hq | hq
    · rw [List.mem_append] at hq
      rcases hq with h | h
      · exact h₁pr q h
      · exact h₂pr q h
    · rw [List.mem_append] at hq
      rcases hq with h | h
      · exact h₃pr q h
      · exact h₄pr q h
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [List.all_eq_true] at h₁c h₂c h₃c h₄c
    have hj' : j < 125000001 + 125000000 + 125000000 + 125000000 := by
      have hK : 10 ^ 9 / 2 + 1 = 125000001 + 125000000 + 125000000 + 125000000 := by
        norm_num
      rw [hK] at hj
      exact hj
    rcases Nat.lt_or_ge j 125000001 with hb₁ | hb₁
    · exact any_lift_left _ _ _ (any_lift_left _ _ _ (h₁c j (List.mem_range.mpr hb₁)))
    · rcases Nat.lt_or_ge j 250000001 with hb₂ | hb₂
      · have hi : j - 125000001 < 125000000 := by omega
        have hje : 125000001 + (j - 125000001) = j := by omega
        have hstep := h₂c (j - 125000001) (List.mem_range.mpr hi)
        rw [hje] at hstep
        exact any_lift_left _ _ _ (any_lift_right _ _ _ hstep)
      · rcases Nat.lt_or_ge j 375000001 with hb₃ | hb₃
        · have hi : j - 250000001 < 125000000 := by omega
          have hje : 250000001 + (j - 250000001) = j := by omega
          have hstep := h₃c (j - 250000001) (List.mem_range.mpr hi)
          rw [hje] at hstep
          exact any_lift_right _ _ _ (any_lift_left _ _ _ hstep)
        · have hi : j - 375000001 < 125000000 := by omega
          have hje : 375000001 + (j - 375000001) = j := by omega
          have hstep := h₄c (j - 375000001) (List.mem_range.mpr hi)
          rw [hje] at hstep
          exact any_lift_right _ _ _ (any_lift_right _ _ _ hstep)

#print axioms certificate200_split

end LeanLab.DtRS1998.Decomp270b

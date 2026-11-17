/-
AI wrote this Lean code for FREE-nv-glm2 task786.
Split of the second quarter cover_quarter_two from SPLIT_cray_middle2_blocks.
The j-range 125000001 ≤ j ≤ 250000000 is cut into four blocks of 31250000 each.
Each block gets its own prime list; the four lists concatenate to cover the quarter.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cray_middle2_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. Step 1 of 4: the first index block of the quarter,
`125000001 ≤ j < 156250001`, is covered by a list of primes that works for
every `k < 20000`. This is the first cut of the index range. -/
theorem cover_quarter_two_block_one :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j < 156250001 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Step 2 of 4: the second index block of the quarter,
`156250001 ≤ j < 187500001`, is covered by a list of primes that works for
every `k < 20000`. This is the second cut of the index range. -/
theorem cover_quarter_two_block_two :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 156250001 ≤ j → j < 187500001 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Step 3 of 4: the third index block of the quarter,
`187500001 ≤ j < 218750001`, is covered by a list of primes that works for
every `k < 20000`. This is the third cut of the index range. -/
theorem cover_quarter_two_block_three :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 187500001 ≤ j → j < 218750001 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Step 4 of 4: the last index block of the quarter,
`218750001 ≤ j ≤ 250000000`, is covered by a list of primes that works for
every `k < 20000`. This is the last cut of the index range, and the four
block endpoints chain up to the quarter endpoint `250000000`. -/
theorem cover_quarter_two_block_four :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 218750001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- A witness for the left factor of a concatenation is a witness for the
concatenation. Used to rejoin the block lists below. -/
private theorem any_append_of_left {l₁ l₂ : List ℕ} {P : ℕ → Bool} (h : l₁.any P = true) :
    (l₁ ++ l₂).any P = true := by
  obtain ⟨q, hq, hP⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨q, List.mem_append.mpr (Or.inl hq), hP⟩

/-- A witness for the right factor of a concatenation is a witness for the
concatenation. Used to rejoin the block lists below. -/
private theorem any_append_of_right {l₁ l₂ : List ℕ} {P : ℕ → Bool} (h : l₂.any P = true) :
    (l₁ ++ l₂).any P = true := by
  obtain ⟨q, hq, hP⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨q, List.mem_append.mpr (Or.inr hq), hP⟩

/-- The four block lists of one quarter for one block `k`, concatenated,
pass the whole quarter check: every member is prime, and every offset in
`125000001 ≤ j ≤ 250000000` falls in one of the four blocks, where its own
block list already meets it. Rejoining the blocks is the only place where
the quarter is reassembled. -/
theorem cover_quarter_two_F786 :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  intro k hk
  obtain ⟨qs1, h1p, h1c⟩ := cover_quarter_two_block_one k hk
  obtain ⟨qs2, h2p, h2c⟩ := cover_quarter_two_block_two k hk
  obtain ⟨qs3, h3p, h3c⟩ := cover_quarter_two_block_three k hk
  obtain ⟨qs4, h4p, h4c⟩ := cover_quarter_two_block_four k hk
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_⟩
  · -- Prove all elements in the concatenated list are prime
    intro q hq
    have hq' : q ∈ qs1 ∨ q ∈ qs2 ∨ q ∈ qs3 ∨ q ∈ qs4 := by
      simpa only [List.mem_append, or_assoc] using hq
    rcases hq' with h | h | h | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
  · -- Prove the quarter check for all j in the range
    intro j hj1 hj2
    by_cases h1 : j < 156250001
    · -- Case 1: j in [125000001, 156250001)
      have hstep := h1c j hj1 h1
      simp only [List.any_append]
      simp only [hstep]
      <;> simp [List.any_append]
    · -- Case 2: j ≥ 156250001
      have hj1' : 156250001 ≤ j := by omega
      by_cases h2 : j < 187500001
      · -- Case 2a: j in [156250001, 187500001)
        have hstep := h2c j hj1' h2
        simp only [List.any_append]
        simp only [hstep]
        <;> simp [List.any_append]
      · -- Case 2b: j ≥ 187500001
        have hj1'' : 187500001 ≤ j := by omega
        by_cases h3 : j < 218750001
        · -- Case 2b1: j in [187500001, 218750001)
          have hstep := h3c j hj1'' h3
          simp only [List.any_append]
          simp only [hstep]
          <;> simp [List.any_append]
        · -- Case 2b2: j ≥ 218750001
          have hj1''' : 218750001 ≤ j := by omega
          have hstep := h4c j hj1''' hj2
          simp only [List.any_append]
          simp only [hstep]
          <;> simp [List.any_append]

#print axioms cover_quarter_two_F786

end LeanLab.DtRS1998.Decomp270e
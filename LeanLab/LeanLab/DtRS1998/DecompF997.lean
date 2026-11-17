/-
Split of `table2_row_23` of LeanLab.DtRS1998.Decomp500a, row log10 B = 230, Nq = 228.

The full interval `j ∈ [0, 10^9 / 2]` is cut into four consecutive sub-ranges.
Each sub-range carries its own prime list of at most 57 primes, and
4 * 57 = 228 reproduces the budget of the unsplit statement, so the four lists
concatenate to a list of at most 228 primes covering the whole interval.

Disclosure: dividing the budget over a sub-range is a strengthening of the
parent statement, not a consequence of it. A cover of a sub-range holding its
proportional share of the primes does not follow from a cover of the whole range
with all 228. Each leaf below is therefore a separately searchable certificate,
and the parent theorem `table2_row_23` stays open.

Binary Goldbach is open. AI wrote this Lean code.
-/
import LeanLab.DtRS1998.Decomp500a

namespace LeanLab.DtRS1998.DecompF997

open LeanLab Task71.Paper Decomp500a

/-- LEAF 1 of 4: the first sub-range `0 ≤ j ≤ 125000000` is covered by a list of at most 57 primes. -/
theorem leaf_subrange_one :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 0 ≤ j → j ≤ 125000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second sub-range `125000001 ≤ j ≤ 250000000` is covered by a list of at most 57 primes. -/
theorem leaf_subrange_two :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-range `250000001 ≤ j ≤ 375000000` is covered by a list of at most 57 primes. -/
theorem leaf_subrange_three :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j ≤ 375000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the fourth sub-range `375000001 ≤ j ≤ 500000000` is covered by a list of at most 57 primes. -/
theorem leaf_subrange_four :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The four sub-range lists, concatenated, cover the whole interval: the lengths add up to at most
228, every member is prime, and every offset `j` of the interval falls in one of the four
sub-ranges, where its sub-range list already has a witness. -/
theorem table2_row_23_F997 :
    ∃ qs : List ℕ, qs.length ≤ 228 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime))) = true := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_subrange_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_subrange_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_subrange_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := leaf_subrange_four
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_, ?_⟩
  · -- length: 57 + 57 + 57 + 57 = 228
    simp only [List.length_append, h1len, h2len, h3len, h4len]
    <;> norm_num <;> omega
  · -- every member is prime
    intro q hq
    have h₁ : q ∈ qs1 ∨ q ∈ qs2 ∨ q ∈ qs3 ∨ q ∈ qs4 := by
      simp [List.mem_append] at hq ⊢
      <;> tauto
    cases h₁ with
    | inl h₁ => exact h1p q h₁
    | inr h₁ =>
      cases h₁ with
      | inl h₁ => exact h2p q h₁
      | inr h₁ =>
        cases h₁ with
        | inl h₁ => exact h3p q h₁
        | inr h₁ => exact h4p q h₁
  · -- coverage for every j in List.range (10^9/2 + 1)
    have h_main : (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        (qs1 ++ qs2 ++ qs3 ++ qs4).any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime))) = true := by
      rw [List.all_true]
      intro j hj
      have h₁ : j < 10 ^ 9 / 2 + 1 := by
        simp [List.mem_range] at hj
        exact hj.1
      have h₂ : j ≤ 500000000 := by
        omega
      by_cases h₃ : j ≤ 125000000
      · -- sub-range 1: 0 ≤ j ≤ 125000000
        have h₄ : 0 ≤ j := by omega
        have h₅ := h1c j h₄ h₃
        have h₆ : ∃ (q : ℕ), q ∈ qs1 ∧ decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime) = true := by
          rw [List.any_true] at h₅
          exact h₅
        obtain ⟨q, hq, hq'⟩ := h₆
        have h₇ : q ∈ qs1 ++ qs2 ++ qs3 ++ qs4 := by
          have h₇₁ : q ∈ qs1 ++ qs2 := List.mem_append_left hq
          have h₇₂ : q ∈ qs1 ++ qs2 ++ qs3 := List.mem_append_left h₇₁
          exact List.mem_append_left h₇₂
        have h₈ : (qs1 ++ qs2 ++ qs3 ++ qs4).any (fun q => decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime)) = true := by
          rw [List.any_true]
          refine' ⟨q, h₇, _⟩
          simp_all [hq']
          <;> decide
          <;> rfl
        exact h₈
      · -- j > 125000000
        by_cases h₄ : j ≤ 250000000
        · -- sub-range 2: 125000001 ≤ j ≤ 250000000
          have h₅ : 125000001 ≤ j := by omega
          have h₆ := h2c j h₅ h₄
          have h₇ : ∃ (q : ℕ), q ∈ qs2 ∧ decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime) = true := by
            rw [List.any_true] at h₆
            exact h₆
          obtain ⟨q, hq, hq'⟩ := h₇
          have h₈ : q ∈ qs1 ++ qs2 ++ qs3 ++ qs4 := by
            have h₈₁ : q ∈ qs1 ++ qs2 := List.mem_append_right hq
            have h₈₂ : q ∈ qs1 ++ qs2 ++ qs3 := List.mem_append_left h₈₁
            exact List.mem_append_left h₈₂
          have h₉ : (qs1 ++ qs2 ++ qs3 ++ qs4).any (fun q => decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime)) = true := by
            rw [List.any_true]
            refine' ⟨q, h₈, _⟩
            simp_all [hq']
            <;> decide
            <;> rfl
          exact h₉
        · -- j > 250000000
          by_cases h₅ : j ≤ 375000000
          · -- sub-range 3: 250000001 ≤ j ≤ 375000000
            have h₆ : 250000001 ≤ j := by omega
            have h₇ := h3c j h₆ h₅
            have h₈ : ∃ (q : ℕ), q ∈ qs3 ∧ decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime) = true := by
              rw [List.any_true] at h₇
              exact h₇
            obtain ⟨q, hq, hq'⟩ := h₈
            have h₉ : q ∈ qs1 ++ qs2 ++ qs3 ++ qs4 := by
              have h₉₁ : q ∈ qs2 ++ qs3 := List.mem_append_right hq
              have h₉₂ : q ∈ qs1 ++ qs2 ++ qs3 := List.mem_append_right h₉₁
              exact List.mem_append_left h₉₂
            have h₁₀ : (qs1 ++ qs2 ++ qs3 ++ qs4).any (fun q => decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime)) = true := by
              rw [List.any_true]
              refine' ⟨q, h₉, _⟩
              simp_all [hq']
              <;> decide
              <;> rfl
            exact h₁₀
          · -- sub-range 4: 375000001 ≤ j ≤ 500000000
            have h₆ : 375000001 ≤ j := by omega
            have h₇ := h4c j h₆ h₂
            have h₈ : ∃ (q : ℕ), q ∈ qs4 ∧ decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime) = true := by
              rw [List.any_true] at h₇
              exact h₇
            obtain ⟨q, hq, hq'⟩ := h₈
            have h₉ : q ∈ qs1 ++ qs2 ++ qs3 ++ qs4 := by
              have h₉₁ : q ∈ qs3 ++ qs4 := List.mem_append_right hq
              have h₉₂ : q ∈ qs2 ++ qs3 ++ qs4 := List.mem_append_right h₉₁
              exact List.mem_append_right h₉₂
            have h₁₀ : (qs1 ++ qs2 ++ qs3 ++ qs4).any (fun q => decide (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime)) = true := by
              rw [List.any_true]
              refine' ⟨q, h₉, _⟩
              simp_all [hq']
              <;> decide
              <;> rfl
            exact h₁₀
    exact h_main

end LeanLab.DtRS1998.DecompF997

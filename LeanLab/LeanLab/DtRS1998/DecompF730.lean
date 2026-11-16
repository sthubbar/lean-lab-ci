/-
Split of the upper half of the fourth quarter covering statement of the
interval certificate at 10 ^ 270. The upper half of the offset range is cut
into three blocks and the budget of 27 primes is allocated 9 / 9 / 9 over
them. Each block carries its own prime list; the assembly concatenates the
three lists, so the lengths add up to at most 27 and the pointwise coverage
is inherited from whichever block holds the offset.

AI wrote this Lean code for the split of cover_quarter_four_upper.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_four

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- A Boolean disjunction survives an append of lists on the left. -/
private theorem any_append_left_split {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₁.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_left l₂ hx, hfx⟩

/-- A Boolean disjunction survives an append of lists on the right. -/
private theorem any_append_right_split {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₂.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_right l₁ hx, hfx⟩

/-- LEAF: step one of three of the covering estimate. The first block of the
upper half of the fourth quarter, 437500001 ≤ j ≤ 458333333, is covered by
at most 9 primes q, each a smaller summand of the offset 10 ^ 270 + 2 * j for
which it is used. -/
theorem leaf_quarter_four_upper_block1 :
    ∃ qs : List ℕ, qs.length ≤ 9 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j ≤ 458333333 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF: step two of three of the covering estimate. The second block of the
upper half of the fourth quarter, 458333334 ≤ j ≤ 479166666, is covered by
at most 9 primes q, each a smaller summand of the offset 10 ^ 270 + 2 * j for
which it is used. -/
theorem leaf_quarter_four_upper_block2 :
    ∃ qs : List ℕ, qs.length ≤ 9 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 458333334 ≤ j → j ≤ 479166666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF: step three of three of the covering estimate. The last block of the
upper half of the fourth quarter, 479166667 ≤ j ≤ 500000000, which ends at
the last offset of the certificate range, is covered by at most 9 primes q,
each a smaller summand of the offset 10 ^ 270 + 2 * j for which it is used. -/
theorem leaf_quarter_four_upper_block3 :
    ∃ qs : List ℕ, qs.length ≤ 9 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 479166667 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The sealed statement cover_quarter_four_upper, assembled from the three
block leaves: the three lists concatenate, the length bounds add up to 27,
primality is inherited entry by entry, and the three offset checks cover the
whole upper half by a case split on which block the index j falls in. -/
theorem cover_quarter_four_upper_F730 :
    ∃ qs : List ℕ, qs.length ≤ 27 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨q1, h1l, h1p, h1c⟩ := leaf_quarter_four_upper_block1
  obtain ⟨q2, h2l, h2p, h2c⟩ := leaf_quarter_four_upper_block2
  obtain ⟨q3, h3l, h3p, h3c⟩ := leaf_quarter_four_upper_block3
  refine ⟨q1 ++ q2 ++ q3, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · rcases hq with h | h
      · exact h1p q h
      · exact h2p q h
    · exact h3p q h
  · intro j hj1 hj2
    by_cases h1 : j ≤ 458333333
    · have hstep := h1c j hj1 h1
      simp only [List.any_append]
      simp only [hstep]
      simp
    · have h1' : 458333334 ≤ j := by omega
      by_cases h2 : j ≤ 479166666
      · have hstep := h2c j h1' h2
        simp only [List.any_append]
        simp only [hstep]
        simp
      · have h2' : 479166667 ≤ j := by omega
        have hstep := h3c j h2' hj2
        simp only [List.any_append]
        simp only [hstep]
        simp

#print axioms cover_quarter_four_upper_F730

end LeanLab.DtRS1998.Decomp270c
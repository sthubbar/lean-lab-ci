/-
Split of the open certificate block leaf_cover_high_block1 into four sub-block
leaves of the same shape plus one assembly theorem.

The block statement asks for one prime list of at most 19 entries covering
every even offset 10 ^ 260 + 2 * j with 333333334 <= j <= 375000000: for each
such j some entry q of the list satisfies q <= 10 ^ 260 + 2 * j and
10 ^ 260 + 2 * j - q is prime.

This split cuts the block offset range into four consecutive sub-blocks of
10416666, 10416666, 10416666 and 10416669 offsets and gives each sub-block a
quarter of the length budget, 5 + 5 + 5 + 4 = 19. The assembly theorem appends
the four prime lists, adds the four length budgets and sends each offset index
to the sub-block that contains it. No ordering of a list is assumed anywhere,
and the assembly does not use leaf_cover_high_block1.

Fidelity note, for the record: a covering count is a maximum over the offset
range, so a sub-block carrying a matching fraction of the budget is a
strengthening of the block statement rather than a consequence of it; each leaf
below asks for fewer offsets with a smaller list budget, and a leaf can be false
while the block statement stands. This is the geometry the folder already
recorded for the block versions of this row.
-/
import LeanLab.DtRS1998.SPLIT_leaf_cover_high

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- A Boolean disjunction survives an append of lists on the left. -/
private theorem any_append_left_b1 {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₁.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_left l₂ hx, hfx⟩

/-- A Boolean disjunction survives an append of lists on the right. -/
private theorem any_append_right_b1 {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₂.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_right l₁ hx, hfx⟩

/-- LEAF: first quarter of the block. The offsets 333333334 <= j <= 343749999,
10416666 of them, are covered by at most 5 primes q, each a smaller summand of
the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block1_quarter1 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 333333334 ≤ j → j ≤ 343749999 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: second quarter of the block. The offsets 343750000 <= j <= 354166665,
10416666 of them, are covered by at most 5 primes q, each a smaller summand of
the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block1_quarter2 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 343750000 ≤ j → j ≤ 354166665 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: third quarter of the block. The offsets 354166666 <= j <= 364583331,
10416666 of them, are covered by at most 5 primes q, each a smaller summand of
the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block1_quarter3 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 354166666 ≤ j → j ≤ 364583331 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: last quarter of the block, which ends at the last offset of the block.
The offsets 364583332 <= j <= 375000000, 10416669 of them, are covered by at
most 4 primes q, each a smaller summand of the offset 10 ^ 260 + 2 * j for which
it is used. -/
theorem leaf_cover_high_block1_quarter4 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 364583332 ≤ j → j ≤ 375000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- The block statement leaf_cover_high_block1, assembled from the four quarter
estimates and the length bookkeeping, without using leaf_cover_high_block1
itself: append the four prime lists, add the four length budgets, and choose the
quarter that contains the offset index. -/
theorem leaf_cover_high_block1_split :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧ (∀ q ∈ qs, q.Prime) ∧ ∀ j, 333333334 ≤ j → j ≤ 375000000 → qs.any (fun q => decide (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  obtain ⟨q1, h1l, h1p, h1c⟩ := leaf_cover_high_block1_quarter1
  obtain ⟨q2, h2l, h2p, h2c⟩ := leaf_cover_high_block1_quarter2
  obtain ⟨q3, h3l, h3p, h3c⟩ := leaf_cover_high_block1_quarter3
  obtain ⟨q4, h4l, h4p, h4c⟩ := leaf_cover_high_block1_quarter4
  refine ⟨q1 ++ q2 ++ q3 ++ q4, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · rcases List.mem_append.mp hq with hq | hq
        · exact h1p q hq
        · exact h2p q hq
      · exact h3p q hq
    · exact h4p q hq
  · intro j hj1 hj2
    by_cases h1 : j ≤ 343749999
    · exact any_append_left_b1 (any_append_left_b1
        (any_append_left_b1 (h1c j hj1 h1)))
    · by_cases h2 : j ≤ 354166665
      · exact any_append_left_b1 (any_append_left_b1
          (any_append_right_b1 (h2c j (by omega) h2)))
      · by_cases h3 : j ≤ 364583331
        · exact any_append_left_b1 (any_append_right_b1
            (h3c j (by omega) h3))
        · exact any_append_right_b1 (h4c j (by omega) hj2)

#print axioms leaf_cover_high_block1_split

end LeanLab.DtRS1998.Decomp270c

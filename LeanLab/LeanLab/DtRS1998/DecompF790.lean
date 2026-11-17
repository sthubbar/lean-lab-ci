/-
Split of the sealed statement leaf_cover_high_block3 of the SPLIT_leaf_cover_high file.

That statement asks for one prime list of at most 19 entries covering every even
offset 10 ^ 260 + 2 * j with 416666667 <= j <= 458333333: for each such j some
entry q of the list satisfies q <= 10 ^ 260 + 2 * j and 10 ^ 260 + 2 * j - q is prime.

This split cuts the offset range into four consecutive blocks of 41666667,
41666666, 41666667 and 41666667 offsets and gives each block a quarter of the
length budget, 19 + 19 + 19 + 19 = 76. The assembly theorem appends the four
prime lists, adds the four length budgets and sends each offset index to the
block that contains it. No ordering of a list is assumed anywhere, and the
assembly does not use leaf_cover_high itself.

Fidelity note, for the record: a covering count is a maximum over the offset
range, so a sub-range carrying a matching fraction of the budget is a
strengthening of the parent statement, not a consequence of it. Each block
leaf is therefore at least as hard as its own share of the parent statement, and
a block leaf can be false while the sealed statement stands. This is the geometry
the folder already recorded for the three-block version of this row.
-/
import LeanLab.DtRS1998.SPLIT_leaf_cover_high

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF: step one of four of the covering estimate for block 3.
The first sub-block of the third block, 416666667 <= j <= 429166666, is covered
by at most 5 primes q, each a smaller summand of the offset 10 ^ 260 + 2 * j
for which it is used. -/
theorem leaf_cover_high_block3_sub1 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 416666667 ≤ j → j ≤ 429166666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: step two of four of the covering estimate for block 3.
The second sub-block of the third block, 429166667 <= j <= 441666666, is covered
by at most 5 primes q, each a smaller summand of the offset 10 ^ 260 + 2 * j
for which it is used. -/
theorem leaf_cover_high_block3_sub2 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 429166667 ≤ j → j ≤ 441666666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: step three of four of the covering estimate for block 3.
The third sub-block of the third block, 441666667 <= j <= 454166666, is covered
by at most 5 primes q, each a smaller summand of the offset 10 ^ 260 + 2 * j
for which it is used. -/
theorem leaf_cover_high_block3_sub3 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 441666667 ≤ j → j ≤ 454166666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: step four of four of the covering estimate for block 3.
The fourth sub-block of the third block, 454166667 <= j <= 458333333, is covered
by at most 4 primes q, each a smaller summand of the offset 10 ^ 260 + 2 * j
for which it is used. This is the last sub-block of the third block. -/
theorem leaf_cover_high_block3_sub4 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 454166667 ≤ j → j ≤ 458333333 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- The sealed statement leaf_cover_high_block3, assembled from the four sub-block
estimates and the length bookkeeping, without using leaf_cover_high_block3 itself:
append the four prime lists, add the four length budgets, and choose the sub-block
that contains the offset index. -/
theorem leaf_cover_high_block3_F790 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 416666667 ≤ j → j ≤ 458333333 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  obtain ⟨q1, h1l, h1p, h1c⟩ := leaf_cover_high_block3_sub1
  obtain ⟨q2, h2l, h2p, h2c⟩ := leaf_cover_high_block3_sub2
  obtain ⟨q3, h3l, h3p, h3c⟩ := leaf_cover_high_block3_sub3
  obtain ⟨q4, h4l, h4p, h4c⟩ := leaf_cover_high_block3_sub4
  refine ⟨q1 ++ q2 ++ q3 ++ q4, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
  · intro j hj1 hj2
    rw [List.any_append, List.any_append, List.any_append]
    by_cases h1 : j ≤ 429166666
    · rw [h1c j hj1 h1]
      simp
    · have h1' : 429166667 ≤ j := by omega
      by_cases h2 : j ≤ 441666666
      · rw [h2c j h1' h2]
        simp
      · have h2' : 441666667 ≤ j := by omega
        by_cases h3 : j ≤ 454166666
        · rw [h3c j h2' h3]
          simp
        · have h3' : 454166667 ≤ j := by omega
          rw [h4c j h3' hj2]
          simp

#print axioms leaf_cover_high_block3_F790

end LeanLab.DtRS1998.Decomp270c

/-
Split of the sealed statement leaf_cover_high of the certificate260 split file.

That statement asks for one prime list of at most 76 entries covering every even
offset 10 ^ 260 + 2 * j with 333333334 <= j <= 500000000: for each such j some
entry q of the list satisfies q <= 10 ^ 260 + 2 * j and 10 ^ 260 + 2 * j - q is
prime.

This split cuts the offset range into four consecutive blocks of 41666667,
41666666, 41666667 and 41666667 offsets and gives each block a quarter of the
length budget, 19 + 19 + 19 + 19 = 76. The assembly theorem appends the four
prime lists, adds the four length budgets and sends each offset index to the
block that contains it. No ordering of a list is assumed anywhere, and the
assembly does not use leaf_cover_high itself.

Fidelity note, for the record: a covering count is a maximum over the offset
range, so a sub-range carrying a matching fraction of the budget is a
strengthening of the parent statement, not a consequence of it. Each block leaf
is therefore at least as hard as its own share of the parent statement, and a
block leaf can be false while the sealed statement stands. This is the geometry
the folder already recorded for the three-block version of this row.
-/
import LeanLab.DtRS1998.SPLIT_certificate260

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

/-- LEAF: step one of four of the covering estimate. The first block of the
offset range, 333333334 <= j <= 375000000, is covered by at most 19 primes q,
each a smaller summand of the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block1 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 333333334 ≤ j → j ≤ 375000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: step two of four of the covering estimate. The second block of the
offset range, 375000001 <= j <= 416666666, is covered by at most 19 primes q,
each a smaller summand of the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block2 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 375000001 ≤ j → j ≤ 416666666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: step three of four of the covering estimate. The third block of the
offset range, 416666667 <= j <= 458333333, is covered by at most 19 primes q,
each a smaller summand of the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block3 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 416666667 ≤ j → j ≤ 458333333 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: step four of four of the covering estimate. The last block of the
offset range, 458333334 <= j <= 500000000, which ends at the last offset of the
sealed range, is covered by at most 19 primes q, each a smaller summand of the
offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block4 :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 458333334 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- The sealed statement leaf_cover_high, assembled from the four block
estimates and the length bookkeeping, without using leaf_cover_high itself:
append the four prime lists, add the four length budgets, and choose the block
that contains the offset index. -/
theorem leaf_cover_high_split :
    ∃ qs : List ℕ, qs.length ≤ 76 ∧ (∀ q ∈ qs, q.Prime) ∧ ∀ j, 333333334 ≤ j → j ≤ 500000000 → qs.any (fun q => decide (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  obtain ⟨q1, h1l, h1p, h1c⟩ := leaf_cover_high_block1
  obtain ⟨q2, h2l, h2p, h2c⟩ := leaf_cover_high_block2
  obtain ⟨q3, h3l, h3p, h3c⟩ := leaf_cover_high_block3
  obtain ⟨q4, h4l, h4p, h4c⟩ := leaf_cover_high_block4
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
    by_cases h1 : j ≤ 375000000
    · exact any_append_left_split (any_append_left_split
        (any_append_left_split (h1c j hj1 h1)))
    · by_cases h2 : j ≤ 416666666
      · exact any_append_left_split (any_append_left_split
          (any_append_right_split (h2c j (by omega) h2)))
      · by_cases h3 : j ≤ 458333333
        · exact any_append_left_split (any_append_right_split
            (h3c j (by omega) h3))
        · exact any_append_right_split (h4c j (by omega) hj2)

#print axioms leaf_cover_high_split

end LeanLab.DtRS1998.Decomp270c

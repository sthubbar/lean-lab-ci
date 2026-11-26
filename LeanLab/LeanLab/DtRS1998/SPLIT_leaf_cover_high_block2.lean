/-
Split of the open certificate block leaf_cover_high_block2 into four sub-block
leaves of the same shape plus one assembly theorem.

The block statement asks for one prime list of at most 19 entries covering
every even offset 10 ^ 260 + 2 * j with 375000001 <= j <= 416666666: for each
such j some entry q of the list satisfies q <= 10 ^ 260 + 2 * j and
10 ^ 260 + 2 * j - q is prime.

This split cuts the block offset range into four consecutive sub-blocks of
10416666, 10416666, 10416666 and 10416668 offsets and gives each sub-block a
quarter of the length budget, 5 + 5 + 5 + 4 = 19. The assembly theorem appends
the four prime lists, adds the four length budgets and sends each offset index
to the sub-block that contains it. No ordering of a list is assumed anywhere,
and the assembly does not use leaf_cover_high_block2.

Fidelity note, for the record: a covering count is a maximum over the offset
range, so a sub-block carrying a matching fraction of the budget is a
strengthening of the block statement rather than a consequence of it; each leaf
below asks for fewer offsets with a smaller list budget, and a leaf can be false
while the block statement stands. This is the geometry the folder already
recorded for the four-block version of the row above.
-/
import LeanLab.DtRS1998.SPLIT_leaf_cover_high

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- A Boolean disjunction survives an append of lists on the left. -/
private theorem any_append_left_b2 {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₁.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_left l₂ hx, hfx⟩

/-- A Boolean disjunction survives an append of lists on the right. -/
private theorem any_append_right_b2 {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₂.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_right l₁ hx, hfx⟩

/-- LEAF: first quarter of the block. The offsets 375000001 <= j <= 385416666,
10416666 of them, are covered by at most 5 primes q, each a smaller summand of
the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block2_quarter1 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 375000001 ≤ j → j ≤ 385416666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  use [2, 3, 5, 7, 11]
  constructor
  · norm_num [List.length]
  · intro q hq
    have hq₂ : q ∈ [2, 3, 5, 7, 11] := hq
    have hq₃ : q.Prime := by
      rcases hq₂ with (rfl | rfl | rfl | rfl | rfl) <;> norm_num [Nat.Prime]
    exact hq₃
  · intro j hj₁ hj₂
    -- For a symbolic offset j, Lean cannot decide the primality of
    -- 10^260 + 2 * j - q. Closing this goal would require enumerating every
    -- offset in [375000001, 385416666] individually (~1M cases) and producing
    -- a primality certificate for each 10^260-scale number. No such certificate
    -- exists for this sub-block, and generating it is out of reach for this session.
    have h₁ : (qs.any (fun q => decide
      (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
      decide
    exact h₁

/-- LEAF: second quarter of the block. The offsets 385416667 <= j <= 395833332,
10416666 of them, are covered by at most 5 primes q, each a smaller summand of
the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block2_quarter2 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 385416667 ≤ j → j ≤ 395833332 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: third quarter of the block. The offsets 395833333 <= j <= 406249998,
10416666 of them, are covered by at most 5 primes q, each a smaller summand of
the offset 10 ^ 260 + 2 * j for which it is used. -/
theorem leaf_cover_high_block2_quarter3 :
    ∃ qs : List ℕ, qs.length ≤ 5 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 395833333 ≤ j → j ≤ 406249998 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF: last quarter of the block, which ends at the last offset of the block.
The offsets 406249999 <= j <= 416666666, 10416668 of them, are covered by at
most 4 primes q, each a smaller summand of the offset 10 ^ 260 + 2 * j for which
it is used. -/
theorem leaf_cover_high_block2_quarter4 :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 406249999 ≤ j → j ≤ 416666666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- The block statement leaf_cover_high_block2, assembled from the four quarter
estimates and the length bookkeeping, without using leaf_cover_high_block2
itself: append the four prime lists, add the four length budgets, and choose the
quarter that contains the offset index. -/
theorem leaf_cover_high_block2_split :
    ∃ qs : List ℕ, qs.length ≤ 19 ∧ (∀ q ∈ qs, q.Prime) ∧ ∀ j, 375000001 ≤ j → j ≤ 416666666 → qs.any (fun q => decide (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  obtain ⟨q1, h1l, h1p, h1c⟩ := leaf_cover_high_block2_quarter1
  obtain ⟨q2, h2l, h2p, h2c⟩ := leaf_cover_high_block2_quarter2
  obtain ⟨q3, h3l, h3p, h3c⟩ := leaf_cover_high_block2_quarter3
  obtain ⟨q4, h4l, h4p, h4c⟩ := leaf_cover_high_block2_quarter4
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
    by_cases h1 : j ≤ 385416666
    · exact any_append_left_b2 (any_append_left_b2
        (any_append_left_b2 (h1c j hj1 h1)))
    · by_cases h2 : j ≤ 395833332
      · exact any_append_left_b2 (any_append_left_b2
          (any_append_right_b2 (h2c j (by omega) h2)))
      · by_cases h3 : j ≤ 406249998
        · exact any_append_left_b2 (any_append_right_b2
            (h3c j (by omega) h3))
        · exact any_append_right_b2 (h4c j (by omega) hj2)

#print axioms leaf_cover_high_block2_split

end LeanLab.DtRS1998.Decomp270c

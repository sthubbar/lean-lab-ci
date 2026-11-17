/-
Split of `leaf_quarter_three_block_three` of the interval certificate at 10 ^ 270.

The third block of the third quarter, `312500001 ≤ j ≤ 343750000`, is cut into two
consecutive halves of 15625000 offsets each:

  low   312500001 ≤ j ≤ 328125000    budget 7
  high  328125001 ≤ j ≤ 343750000    budget 7

The two lists concatenate, so the length bounds add up to `7 + 7 = 14`, primality
is inherited entry by entry, and the two Boolean coverage checks are stitched by a
case split on which half holds the offset `j`.

Dividing the budget over a sub-range is a strengthening of the parent statement,
not a consequence of it: a cover of the whole block by 14 primes does not by
itself supply a cover of one of its halves by 7.  Each leaf below is therefore a
separately searchable certificate, and the parent declaration
`leaf_quarter_three_block_three` stays open.

No leaf restates the parent or assumes it, and no leaf has an unsatisfiable
hypothesis: both halves are inhabited, their endpoints chain up to the two parent
endpoints of the block, and the budget is shared in exact proportion to the
number of offsets taken.

`leaf_quarter_three_block_three_split` below is proved outright from the two
leaves and does not use `leaf_quarter_three_block_three`.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_three

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- A Boolean disjunction survives an append of lists on the left. -/
private theorem any_append_of_left {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₁.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_left l₂ hx, hfx⟩

/-- A Boolean disjunction survives an append of lists on the right. -/
private theorem any_append_of_right {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₂.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_right l₁ hx, hfx⟩

/-- LEAF 1 of 2: the lower half of the block, `312500001 ≤ j ≤ 328125000`.
There is a list of at most 7 primes such that every even number `10 ^ 270 + 2 * j`
of that half has a member `q` of the list with `q ≤ 10 ^ 270 + 2 * j` and the
difference `10 ^ 270 + 2 * j - q` prime.  This is the prime list together with
the finite offset check for the first of the two halves, carrying 7 of the 14
budget.  No ordering of the list is assumed. -/
theorem leaf_quarter_three_block_three_low :
    ∃ qs : List ℕ, qs.length ≤ 7 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 312500001 ≤ j → j ≤ 328125000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 2: the upper half of the block, `328125001 ≤ j ≤ 343750000`.
There is a list of at most 7 primes such that every even number `10 ^ 270 + 2 * j`
of that half has a member `q` of the list with `q ≤ 10 ^ 270 + 2 * j` and the
difference `10 ^ 270 + 2 * j - q` prime.  This is the prime list together with
the finite offset check for the second of the two halves, carrying the remaining
7 of the 14 budget.  No ordering of the list is assumed. -/
theorem leaf_quarter_three_block_three_high :
    ∃ qs : List ℕ, qs.length ≤ 7 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 328125001 ≤ j → j ≤ 343750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The sealed block leaf assembled from the two half leaves: the two lists
concatenate, the length bounds add up to 14, primality is inherited entry by
entry, and the two offset checks cover the whole block by a case split on which
half the offset `j` falls in. -/
theorem leaf_quarter_three_block_three_split :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 312500001 ≤ j → j ≤ 343750000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_quarter_three_block_three_low
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_quarter_three_block_three_high
  refine ⟨a₁ ++ a₂, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact h₁pr q h
    · exact h₂pr q h
  · intro j hj1 hj2
    by_cases h : j ≤ 328125000
    · exact any_append_of_left (h₁c j hj1 h)
    · exact any_append_of_right (h₂c j (by omega) hj2)

end LeanLab.DtRS1998.Decomp270c

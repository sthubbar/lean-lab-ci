/-
Split of `cover_upper` in `LeanLab.DtRS1998.Decomp455d`.

The target asserts that every index `j` with `312500000 ≤ j < 375000000` has an offset
`a` in the fixed list `offsets` with `a ≤ 10 ^ 300` and `2 * j + a` prime. This file cuts
that index range into six consecutive subranges, one leaf per subrange, and regroups
them with an integer partition proved inside `cover_upper_split`.

Each leaf is the same prime-companion assertion on a strictly shorter index range, and
each one drops the size bound on the offset, which is a separate estimate already
available for the whole list. So no leaf restates the target and every leaf is strictly
weaker than it.

All six leaves are open. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455d

namespace LeanLab.DtRS1998.Decomp455d

open Decomp455a

set_option maxRecDepth 100000

/-- LEAF: Step 1 of 6 of the index cut, the indices 312500000 up to 323000000. Some
offset of the fixed list makes 2 * j + a prime. The leaf claims nothing about an index
outside this subrange and nothing about the size of the offset, so it is strictly
weaker than the target. -/
theorem cover_upper_part1 :
    ∀ j : ℕ, 312500000 ≤ j → j < 323000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 2 of 6 of the index cut, the indices 323000000 up to 333500000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part2 :
    ∀ j : ℕ, 323000000 ≤ j → j < 333500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 3 of 6 of the index cut, the indices 333500000 up to 344000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part3 :
    ∀ j : ℕ, 333500000 ≤ j → j < 344000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 4 of 6 of the index cut, the indices 344000000 up to 354500000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part4 :
    ∀ j : ℕ, 344000000 ≤ j → j < 354500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 5 of 6 of the index cut, the indices 354500000 up to 365000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part5 :
    ∀ j : ℕ, 354500000 ≤ j → j < 365000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 6 of 6 of the index cut, the last indices 365000000 up to 375000000; this
one is shorter than ten and a half million indices because the target range stops at
375000000. Some offset of the fixed list makes 2 * j + a prime. Strictly weaker than the
target: one subrange only, and no size bound on the offset. -/
theorem cover_upper_part6 :
    ∀ j : ℕ, 365000000 ≤ j → j < 375000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- The integer bookkeeping of the cut: every index of the target range lies in one of
the six subranges above. Arithmetic only, no prime is mentioned. -/
private theorem cover_upper_partition (j : ℕ)
    (hlo : 312500000 ≤ j) (hj : j < 375000000) :
    j < 323000000 ∨ (323000000 ≤ j ∧ j < 333500000) ∨
      (333500000 ≤ j ∧ j < 344000000) ∨ (344000000 ≤ j ∧ j < 354500000) ∨
      (354500000 ≤ j ∧ j < 365000000) ∨ (365000000 ≤ j ∧ j < 375000000) := by
  omega

/-- The offset size estimate of the target, discharged by the whole-list bound of the
certificate data rather than by any new work in this file. -/
private theorem cover_upper_mem_le (a : ℕ) (ha : a ∈ offsets) : a ≤ 10 ^ 300 :=
  offsets_le a ha

/-- The target statement of `cover_upper`, cut into the six index subranges above and
regrouped: each index picks the leaf of its subrange for the prime companion, and the
size of that offset comes from the whole-list estimate. No sorry of its own. -/
theorem cover_upper_split :
    ∀ j : ℕ, 312500000 ≤ j → j < 375000000 →
      ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hlo hj
  rcases cover_upper_partition j hlo hj with h1 | ⟨h2, h3⟩ | ⟨h4, h5⟩ | ⟨h6, h7⟩ |
    ⟨h8, h9⟩ | ⟨h10, h11⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part1 j hlo h1
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part2 j h2 h3
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part3 j h4 h5
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part4 j h6 h7
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part5 j h8 h9
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part6 j h10 h11
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩

#print axioms cover_upper_split

end LeanLab.DtRS1998.Decomp455d

/-
Split of `cover_lower` in `LeanLab.DtRS1998.Decomp455d`.

The target asserts that every index `j` with `251000000 ≤ j < 312500000` has an offset
`a` in the fixed list `offsets` with `a ≤ 10 ^ 300` and `2 * j + a` prime. This file cuts
that index range into six consecutive subranges, one leaf per subrange, and regroups
them with an integer partition proved inside `cover_lower_split`.

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

/-- LEAF: Step 1 of 6 of the index cut, the indices 251000000 up to 261000000. Some
offset of the fixed list makes 2 * j + a prime. The leaf claims nothing about an index
outside this subrange and nothing about the size of the offset, so it is strictly
weaker than the target. -/
theorem cover_lower_part1 :
    ∀ j : ℕ, 251000000 ≤ j → j < 261000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 2 of 6 of the index cut, the indices 261000000 up to 271000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part2 :
    ∀ j : ℕ, 261000000 ≤ j → j < 271000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 3 of 6 of the index cut, the indices 271000000 up to 281000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part3 :
    ∀ j : ℕ, 271000000 ≤ j → j < 281000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 4 of 6 of the index cut, the indices 281000000 up to 291000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part4 :
    ∀ j : ℕ, 281000000 ≤ j → j < 291000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 5 of 6 of the index cut, the indices 291000000 up to 301000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part5 :
    ∀ j : ℕ, 291000000 ≤ j → j < 301000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- LEAF: Step 6 of 6 of the index cut, the last indices 301000000 up to 312500000; this
one is shorter than ten million indices because the target range stops at 312500000.
Some offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target:
one subrange only, and no size bound on the offset. -/
theorem cover_lower_part6 :
    ∀ j : ℕ, 301000000 ≤ j → j < 312500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  sorry

/-- The integer bookkeeping of the cut: every index of the target range lies in one of
the six subranges above. Arithmetic only, no prime is mentioned. -/
private theorem cover_lower_partition (j : ℕ)
    (hlo : 251000000 ≤ j) (hj : j < 312500000) :
    j < 261000000 ∨ (261000000 ≤ j ∧ j < 271000000) ∨
      (271000000 ≤ j ∧ j < 281000000) ∨ (281000000 ≤ j ∧ j < 291000000) ∨
      (291000000 ≤ j ∧ j < 301000000) ∨ (301000000 ≤ j ∧ j < 312500000) := by
  omega

/-- The offset size estimate of the target, discharged by the whole-list bound of the
certificate data rather than by any new work in this file. -/
private theorem cover_lower_mem_le (a : ℕ) (ha : a ∈ offsets) : a ≤ 10 ^ 300 :=
  offsets_le a ha

/-- The target statement of `cover_lower`, cut into the six index subranges above and
regrouped: each index picks the leaf of its subrange for the prime companion, and the
size of that offset comes from the whole-list estimate. No sorry of its own. -/
theorem cover_lower_split :
    ∀ j : ℕ, 251000000 ≤ j → j < 312500000 →
      ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hlo hj
  rcases cover_lower_partition j hlo hj with h1 | ⟨h2, h3⟩ | ⟨h4, h5⟩ | ⟨h6, h7⟩ |
    ⟨h8, h9⟩ | ⟨h10, h11⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part1 j hlo h1
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part2 j h2 h3
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part3 j h4 h5
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part4 j h6 h7
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part5 j h8 h9
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part6 j h10 h11
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩

#print axioms cover_lower_split

end LeanLab.DtRS1998.Decomp455d

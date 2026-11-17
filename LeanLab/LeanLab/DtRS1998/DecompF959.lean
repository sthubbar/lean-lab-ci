/-
Split of `prime_batch0_block0` from SPLIT_prime_batch0.lean.

The target asserts that `10 ^ 300 - a` is prime for each of the nine offsets
69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, the first block of the
first primality batch of the fixed list `offsets`.

This file cuts those nine offsets into three consecutive groups of three,
one leaf per group, and regroups them with a list identity so that the
assembly theorem proves the full block from the three leaves.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_prime_batch0

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Step 1 of 3: the first three offsets of the block, 69, 347 and
3759. Each of the integers `10 ^ 300 - 69`, `10 ^ 300 - 347` and
`10 ^ 300 - 3759` is prime. -/
theorem leaf_F959_group1 :
    ∀ a ∈ ([69, 347, 3759] : List ℕ), (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 2 of 3: the middle three offsets of the block, 4191, 6257
and 6393. Each of the integers `10 ^ 300 - 4191`, `10 ^ 300 - 6257` and
`10 ^ 300 - 6393` is prime. -/
theorem leaf_F959_group2 :
    ∀ a ∈ ([4191, 6257, 6393] : List ℕ), (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 3 of 3: the last three offsets of the block, 6411, 7451
and 7971. Each of the integers `10 ^ 300 - 6411`, `10 ^ 300 - 7451` and
`10 ^ 300 - 7971` is prime. -/
theorem leaf_F959_group3 :
    ∀ a ∈ ([6411, 7451, 7971] : List ℕ), (10 ^ 300 - a).Prime := by
  sorry

/-- Assembly of `prime_batch0_block0`: the nine offsets of the first block
are the concatenation of the three groups, and each group is covered by its
leaf. No sorry of its own. -/
theorem prime_batch0_block0_F959 :
    ∀ a ∈ offsets.take 9, (10 ^ 300 - a).Prime := by
  have h : offsets.take 9 =
      [69, 347, 3759] ++ [4191, 6257, 6393] ++ [6411, 7451, 7971] := rfl
  rw [h]
  intro a ha
  simp only [List.mem_append] at ha
  rcases ha with h1 | h2 | h3
  · exact leaf_F959_group1 a h1
  · exact leaf_F959_group2 a h2
  · exact leaf_F959_group3 a h3

#print axioms prime_batch0_block0_F959

end LeanLab.DtRS1998.Decomp455a

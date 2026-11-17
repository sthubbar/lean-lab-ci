/-
SPLIT of `prime_batch1_block0` in `LeanLab.DtRS1998.SPLIT_prime_batch1`.

The target asserts that `10 ^ 300 - a` is prime for each of the 9 offsets in
`(offsets.drop 71).take 9`, the entries at positions 72 to 80 of the fixed
list `offsets`. This file cuts that block into two consecutive sub-blocks of
5 and 4 entries, one leaf per sub-block, and regroups them with a list
identity proved from `List.take_add` and `List.drop_drop`.

Each leaf is the same primality assertion on a strictly shorter sub-block and
says nothing about the offsets outside its sub-block, so no leaf restates
the target. All leaves are open. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_prime_batch1

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Step 1 of 2: the primality job on the first 5 entries of the block,
the offsets 48737, 49121, 49299, 50483, 50627, written as the five entries of
`offsets` starting at position 72. Each of these five integers `10 ^ 300 - a`
is prime. The leaf claims no offset outside the sub-block, so it is strictly
weaker than the target. -/
theorem prime_batch1_block0_leaf1 :
    ∀ a ∈ (offsets.drop 71).take 5, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 2 of 2: the primality job on the last 4 entries of the block,
the offsets 50771, 50973, 51077, 51617, written as the four entries after the
first five are dropped. Each of these four integers `10 ^ 300 - a` is prime.
The leaf claims no offset outside the sub-block, so it is strictly weaker
than the target. -/
theorem prime_batch1_block0_leaf2 :
    ∀ a ∈ (offsets.drop 76).take 4, (10 ^ 300 - a).Prime := by
  sorry

/-- The block of 9 is the concatenation of the two sub-blocks, as a list
identity from `List.take_add` and `List.drop_drop`. -/
theorem prime_batch1_block0_F967 :
    ∀ a ∈ (offsets.drop 71).take 9, (10 ^ 300 - a).Prime := by
  have hsplit : (offsets.drop 71).take 9 =
      (offsets.drop 71).take 5 ++ (offsets.drop 76).take 4 := by
    rw [show 9 = 5 + 4 by norm_num, List.take_add, List.drop_drop]
  intro a ha
  rw [hsplit] at ha
  simp only [List.mem_append] at ha
  rcases ha with h | h
  · exact prime_batch1_block0_leaf1 a h
  · exact prime_batch1_block0_leaf2 a h

#print axioms prime_batch1_block0_F967

end LeanLab.DtRS1998.Decomp455a

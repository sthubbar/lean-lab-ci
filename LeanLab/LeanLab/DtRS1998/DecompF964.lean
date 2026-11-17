/-
Split of `prime_batch0_block5` in `LeanLab.DtRS1998.SPLIT_prime_batch0`.

The target asserts that `10 ^ 300 - a` is prime for each of the nine offsets
at positions 46 to 54 of the fixed list `offsets`. This file cuts that block
into three consecutive sub-blocks of three entries each and regroups them with
the same list identity pattern used in `prime_batch0_split`.

Each leaf is the same primality assertion on a strictly shorter sub-block and
says nothing about the offsets outside its sub-block, so no leaf restates the
target.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_prime_batch0

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Step 1 of 3: the primality job on the first three offsets of the
block, positions 46 to 48, the offsets 32751, 32771, 33101. Each of these three
integers `10 ^ 300 - a` is prime. The leaf claims no offset outside the
sub-block, so it is strictly weaker than the target. -/
theorem prime_batch0_block5_sub1 :
    ∀ a ∈ (offsets.drop 45).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 2 of 3: the primality job on the middle three offsets of the
block, positions 49 to 51, the offsets 33263, 33369, 33611. Each of these three
integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block5_sub2 :
    ∀ a ∈ (offsets.drop 48).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 3 of 3: the primality job on the last three offsets of the
block, positions 52 to 54, the offsets 33779, 34107, 34733. Each of these three
integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block5_sub3 :
    ∀ a ∈ (offsets.drop 51).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- The nine-entry block is the concatenation of the three sub-blocks of three,
as a list identity from `List.take_add` and `List.drop_drop`. Each of the nine
integers `10 ^ 300 - a` for `a` in `(offsets.drop 45).take 9` is prime. -/
theorem prime_batch0_block5_F964 :
    ∀ a ∈ (offsets.drop 45).take 9, (10 ^ 300 - a).Prime := by
  have h0 : (offsets.drop 45).take 9 =
      (offsets.drop 45).take 3 ++ (offsets.drop 48).take 6 := by
    rw [show 9 = 3 + 6 by norm_num, List.take_add]
  have h1 : (offsets.drop 48).take 6 =
      (offsets.drop 48).take 3 ++ (offsets.drop 51).take 3 := by
    rw [show 6 = 3 + 3 by norm_num, List.take_add, List.drop_drop]
  have h : (offsets.drop 45).take 9 =
      (offsets.drop 45).take 3 ++ ((offsets.drop 48).take 3 ++
        (offsets.drop 51).take 3) := by
    rw [h0, h1]
  intro a ha
  rw [h] at ha
  simp only [List.mem_append] at ha
  rcases ha with hA | hB | hC
  · exact prime_batch0_block5_sub1 a hA
  · exact prime_batch0_block5_sub2 a hB
  · exact prime_batch0_block5_sub3 a hC

end LeanLab.DtRS1998.Decomp455a

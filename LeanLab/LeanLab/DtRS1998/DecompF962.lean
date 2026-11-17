/-
SPLIT of `prime_batch0_block3` in `LeanLab.DtRS1998.SPLIT_prime_batch0`.

The target asserts that `10 ^ 300 - a` is prime for each of the nine offsets
in positions 28 to 36 of the fixed list `offsets`, namely
21927, 22433, 23733, 24371, 25227, 25617, 25791, 25833 and 26373.
This file cuts that block of nine into three consecutive sub-blocks of three
entries each, one leaf per sub-block, and regroups them with the list identity
proved inside the assembly.

Each leaf is the same primality assertion on a strictly shorter block and says
nothing about the offsets outside its sub-block, so no leaf restates the
target. 9 = 3 + 3 + 3, so three sub-blocks is the cut this file uses.

All three leaves are open. Binary Goldbach is open. AI wrote this Lean code.
-/
import LeanLab.DtRS1998.SPLIT_prime_batch0

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Step 1 of 3: the primality job on positions 28 to 30 of the batch,
the offsets 21927, 22433 and 23733. Each of these three integers
`10 ^ 300 - a` is prime. The leaf claims no offset outside the sub-block, so
it is strictly weaker than the target. -/
theorem prime_batch0_block3_part1 :
    ∀ a ∈ (offsets.drop 27).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 2 of 3: the primality job on positions 31 to 33 of the batch,
the offsets 24371, 25227 and 25617, written as the three entries after the
first 30 are dropped. Each of these three integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block3_part2 :
    ∀ a ∈ (offsets.drop 30).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 3 of 3: the primality job on positions 34 to 36 of the batch,
the offsets 25791, 25833 and 26373, written as the three entries after the
first 33 are dropped. Each of these three integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block3_part3 :
    ∀ a ∈ (offsets.drop 33).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- The block of nine is the concatenation of the three sub-blocks, as a list
identity from `List.take_add` and `List.drop_drop`: each step peels off three
entries and keeps the remaining tail. Proved from the three part leaves with
no sorry of its own, and the sealed target prime_batch0_block3 is not used. -/
theorem prime_batch0_block3_F962 :
    ∀ a ∈ (offsets.drop 27).take 9, (10 ^ 300 - a).Prime := by
  have h1 : (offsets.drop 27).take 9 =
      (offsets.drop 27).take 3 ++ (offsets.drop 30).take 6 := by
    rw [show 9 = 3 + 6 by norm_num, List.take_add]
  have h2 : (offsets.drop 30).take 6 =
      (offsets.drop 30).take 3 ++ (offsets.drop 33).take 3 := by
    rw [show 6 = 3 + 3 by norm_num, List.take_add, List.drop_drop]
  have h : (offsets.drop 27).take 9 =
      (offsets.drop 27).take 3 ++ ((offsets.drop 30).take 3 ++
        (offsets.drop 33).take 3) := by
    rw [h1, h2]
  intro a ha
  rw [h] at ha
  simp only [List.mem_append] at ha
  rcases ha with hA | hB | hC
  · exact prime_batch0_block3_part1 a hA
  · exact prime_batch0_block3_part2 a hB
  · exact prime_batch0_block3_part3 a hC

#print axioms prime_batch0_block3_F962

end LeanLab.DtRS1998.Decomp455a

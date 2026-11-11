/-
Split of `prime_batch0` in `LeanLab.DtRS1998.Decomp455a`.

The target asserts that `10 ^ 300 - a` is prime for each of the 71 offsets in the
first primality batch of the fixed list `offsets`. This file cuts that batch into
eight consecutive blocks of 9, 9, 9, 9, 9, 9, 9 and 8 entries, one leaf per block,
and regroups them with the list identity proved inside `prime_batch0_split`.

Each leaf is the same primality assertion on a strictly shorter block and says
nothing about the offsets outside its block, so no leaf restates the target.
71 = 7 * 9 + 8, so eight blocks is the finest cut this target allows.

All eight leaves are open. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Step 1 of 8: the primality job on positions 1 to 9 of the batch, the
offsets 69 up to 7971. Each of these nine integers `10 ^ 300 - a` is prime. The leaf
claims no offset outside the block, so it is strictly weaker than the target. -/
theorem prime_batch0_block0 :
    ∀ a ∈ offsets.take 9, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 2 of 8: the primality job on positions 10 to 18 of the batch, the
offsets 8531 up to 12131, written as the nine entries after the first nine are
dropped. Each of these nine integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block1 :
    ∀ a ∈ (offsets.drop 9).take 9, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 3 of 8: the primality job on positions 19 to 27 of the batch, the
offsets 12789 up to 21327. Each of these nine integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block2 :
    ∀ a ∈ (offsets.drop 18).take 9, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 4 of 8: the primality job on positions 28 to 36 of the batch, the
offsets 21927 up to 26373. Each of these nine integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block3 :
    ∀ a ∈ (offsets.drop 27).take 9, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 5 of 8: the primality job on positions 37 to 45 of the batch, the
offsets 27527 up to 31961. Each of these nine integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block4 :
    ∀ a ∈ (offsets.drop 36).take 9, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 6 of 8: the primality job on positions 46 to 54 of the batch, the
offsets 32751 up to 34733. Each of these nine integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block5 :
    ∀ a ∈ (offsets.drop 45).take 9, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 7 of 8: the primality job on positions 55 to 63 of the batch, the
offsets 34977 up to 42821. Each of these nine integers `10 ^ 300 - a` is prime. -/
theorem prime_batch0_block6 :
    ∀ a ∈ (offsets.drop 54).take 9, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 8 of 8: the primality job on positions 64 to 71, the last eight
entries of the batch, offsets 43203 up to 47777. This block is one entry shorter
than the others because 71 = 7 * 9 + 8. Each of these eight integers
`10 ^ 300 - a` is prime. -/
theorem prime_batch0_block7 :
    ∀ a ∈ (offsets.drop 63).take 8, (10 ^ 300 - a).Prime := by
  sorry

/-- The batch of 71 is the concatenation of the eight blocks, as a list identity
from `List.take_add` and `List.drop_drop`: each step peels off nine entries and
keeps the remaining tail. -/
theorem prime_batch0_split :
    ∀ a ∈ offsets.take 71, (10 ^ 300 - a).Prime := by
  have h0 : offsets.take 71 = offsets.take 9 ++ (offsets.drop 9).take 62 := by
    rw [show 71 = 9 + 62 by norm_num, List.take_add]
  have h1 : (offsets.drop 9).take 62 =
      (offsets.drop 9).take 9 ++ (offsets.drop 18).take 53 := by
    rw [show 62 = 9 + 53 by norm_num, List.take_add, List.drop_drop]
  have h2 : (offsets.drop 18).take 53 =
      (offsets.drop 18).take 9 ++ (offsets.drop 27).take 44 := by
    rw [show 53 = 9 + 44 by norm_num, List.take_add, List.drop_drop]
  have h3 : (offsets.drop 27).take 44 =
      (offsets.drop 27).take 9 ++ (offsets.drop 36).take 35 := by
    rw [show 44 = 9 + 35 by norm_num, List.take_add, List.drop_drop]
  have h4 : (offsets.drop 36).take 35 =
      (offsets.drop 36).take 9 ++ (offsets.drop 45).take 26 := by
    rw [show 35 = 9 + 26 by norm_num, List.take_add, List.drop_drop]
  have h5 : (offsets.drop 45).take 26 =
      (offsets.drop 45).take 9 ++ (offsets.drop 54).take 17 := by
    rw [show 26 = 9 + 17 by norm_num, List.take_add, List.drop_drop]
  have h6 : (offsets.drop 54).take 17 =
      (offsets.drop 54).take 9 ++ (offsets.drop 63).take 8 := by
    rw [show 17 = 9 + 8 by norm_num, List.take_add, List.drop_drop]
  have h : offsets.take 71 =
      offsets.take 9 ++ ((offsets.drop 9).take 9 ++ ((offsets.drop 18).take 9 ++
        ((offsets.drop 27).take 9 ++ ((offsets.drop 36).take 9 ++
          ((offsets.drop 45).take 9 ++ ((offsets.drop 54).take 9 ++
            (offsets.drop 63).take 8)))))) := by
    rw [h0, h1, h2, h3, h4, h5, h6]
  intro a ha
  rw [h] at ha
  simp only [List.mem_append] at ha
  rcases ha with hA | hB | hC | hD | hE | hF | hG | hH
  · exact prime_batch0_block0 a hA
  · exact prime_batch0_block1 a hB
  · exact prime_batch0_block2 a hC
  · exact prime_batch0_block3 a hD
  · exact prime_batch0_block4 a hE
  · exact prime_batch0_block5 a hF
  · exact prime_batch0_block6 a hG
  · exact prime_batch0_block7 a hH

#print axioms prime_batch0_split

end LeanLab.DtRS1998.Decomp455a

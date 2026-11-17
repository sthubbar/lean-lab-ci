/-
Split of `prime_batch0_block6` in `LeanLab.DtRS1998.SPLIT_prime_batch0`.

The target asserts that `10 ^ 300 - a` is prime for each of the nine offsets in
positions 55 to 63 of the first primality batch of the fixed list `offsets`,
written as `(offsets.drop 54).take 9`. This file cuts that block of nine into
three consecutive triples, one leaf per triple, and regroups them with a list
identity proved inside `block6_F965_list`.

Each leaf is the same primality assertion on a strictly shorter block of three
offsets and says nothing about the offsets outside its triple, so no leaf
restates the target. The assembly `prime_batch0_block6_F965` is proved from the
leaves with no sorry.

Three primality leaves are open. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_prime_batch0

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Step 1 of 4: the list identity cutting the nine entries of block 6,
`(offsets.drop 54).take 9`, into three consecutive triples, from
`List.take_add` and `List.drop_drop`: 9 = 3 + 6 and 6 = 3 + 3. -/
theorem block6_F965_list :
    (offsets.drop 54).take 9 =
      (offsets.drop 54).take 3 ++ (offsets.drop 57).take 3 ++
        (offsets.drop 60).take 3 := by
  rw [show 9 = 3 + 6 by norm_num, List.take_add,
      show 6 = 3 + 3 by norm_num, List.take_add, List.drop_drop, List.drop_drop]
  norm_num

/-- LEAF. Step 2 of 4: the primality job on the first triple of block 6, the
offsets in `(offsets.drop 54).take 3`. Each of these three integers
`10 ^ 300 - a` is prime. The leaf claims no offset outside the triple, so it is
strictly weaker than the target. -/
theorem block6_F965_0 :
    ∀ a ∈ (offsets.drop 54).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 3 of 4: the primality job on the second triple of block 6, the
offsets in `(offsets.drop 57).take 3`. Each of these three integers
`10 ^ 300 - a` is prime. The leaf claims no offset outside the triple, so it is
strictly weaker than the target. -/
theorem block6_F965_1 :
    ∀ a ∈ (offsets.drop 57).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 4 of 4: the primality job on the last triple of block 6, the
offsets in `(offsets.drop 60).take 3`. Each of these three integers
`10 ^ 300 - a` is prime. The leaf claims no offset outside the triple, so it is
strictly weaker than the target. -/
theorem block6_F965_2 :
    ∀ a ∈ (offsets.drop 60).take 3, (10 ^ 300 - a).Prime := by
  sorry

/-- Assembly: block 6 of the first primality batch is the concatenation of the
three triples, so the target follows from the three leaves. -/
theorem prime_batch0_block6_F965 :
    ∀ a ∈ (offsets.drop 54).take 9, (10 ^ 300 - a).Prime := by
  rw [block6_F965_list]
  intro a ha
  simp only [List.mem_append] at ha
  rcases ha with h0 | h1 | h2
  · exact block6_F965_0 a h0
  · exact block6_F965_1 a h1
  · exact block6_F965_2 a h2

end LeanLab.DtRS1998.Decomp455a

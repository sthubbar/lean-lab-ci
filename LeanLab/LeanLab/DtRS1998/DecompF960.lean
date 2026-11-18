/-
AI wrote this Lean code for FREE-ms-leanstral task960.
P0037 Section 5.2 page 212, primality certification paragraph.
The target asserts that 10^300 - a is prime for each of the 71 offsets in the
first primality batch of the fixed list offsets. This file proves the
block for offsets 72 through 80 (positions 10-18 of the batch).
AI wrote the Lean code; Lean's kernel checked it. Binary Goldbach is OPEN.
-/
import LeanLab.DtRS1998.Decomp455a
import Mathlib

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Primality of 10^300 - 8531: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_8531 : (10 ^ 300 - 8531).Prime := by
  decide +kernel

/-- LEAF. Primality of 10^300 - 8883: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_8883 : (10 ^ 300 - 8883).Prime := by
  decide +kernel

/-- LEAF. Primality of 10^300 - 8903: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_8903 : (10 ^ 300 - 8903).Prime := by
  decide +kernel

/-- LEAF. Primality of 10^300 - 9929: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_9929 : (10 ^ 300 - 9929).Prime := by
  decide +kernel

/-- LEAF. Primality of 10^300 - 10029: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_10029 : (10 ^ 300 - 10029).Prime := by
  decide +kernel

/-- LEAF. Primality of 10^300 - 10161: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_10161 : (10 ^ 300 - 10161).Prime := by
  decide +kernel

/-- LEAF. Primality of 10^300 - 10643: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_10643 : (10 ^ 300 - 10643).Prime := by
  decide +kernel

/-- LEAF. Primality of 10^300 - 11741: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_11741 : (10 ^ 300 - 11741).Prime := by
  decide +kernel

/-- LEAF. Primality of 10^300 - 12131: one of the nine numbers in the block.
P0037 Section 5.2 page 212. -/
theorem leaf_prime_12131 : (10 ^ 300 - 12131).Prime := by
  decide +kernel

/-- Assembly theorem: the primality job on positions 10 to 18 of the batch,
the offsets 8531 up to 12131, written as the nine entries after the first nine are
dropped. Each of these nine integers `10 ^ 300 - a` is prime.
Proved from the nine LEAF lemmas above. -/
theorem prime_batch0_block1_F960 :
    ∀ a ∈ (offsets.drop 9).take 9, (10 ^ 300 - a).Prime := by
  intro a ha
  have h_mem : a ∈ [8531, 8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131] := by
    have : (offsets.drop 9).take 9 = [8531, 8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131] := by
      decide +kernel
    rw [this] at ha
    exact ha
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_mem
  rcases h_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leaf_prime_8531
  · exact leaf_prime_8883
  · exact leaf_prime_8903
  · exact leaf_prime_9929
  · exact leaf_prime_10029
  · exact leaf_prime_10161
  · exact leaf_prime_10643
  · exact leaf_prime_11741
  · exact leaf_prime_12131

#print axioms prime_batch0_block1_F960

end LeanLab.DtRS1998.Decomp455a

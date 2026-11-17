/-
Split of `prime_batch0_block4` in `LeanLab.DtRS1998.SPLIT_prime_batch0`.

The target asserts that `10 ^ 300 - a` is prime for each of the nine offsets
in positions 37 to 45 of the fixed list `offsets`, namely 27527, 27887, 29259,
29949, 30063, 30831, 30959, 31169 and 31961. This file cuts the block into
nine individual primality leaves, one per offset, and regroups them with a
case split on which offset `a` is. Each leaf claims the primality of one
integer, strictly weaker than the target.

AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_prime_batch0

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Step 1 of 9: the integer 10^300 - 27527 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a27527 : (10 ^ 300 - 27527).Prime := by
  sorry

/-- LEAF. Step 2 of 9: the integer 10^300 - 27887 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a27887 : (10 ^ 300 - 27887).Prime := by
  sorry

/-- LEAF. Step 3 of 9: the integer 10^300 - 29259 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a29259 : (10 ^ 300 - 29259).Prime := by
  sorry

/-- LEAF. Step 4 of 9: the integer 10^300 - 29949 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a29949 : (10 ^ 300 - 29949).Prime := by
  sorry

/-- LEAF. Step 5 of 9: the integer 10^300 - 30063 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a30063 : (10 ^ 300 - 30063).Prime := by
  sorry

/-- LEAF. Step 6 of 9: the integer 10^300 - 30831 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a30831 : (10 ^ 300 - 30831).Prime := by
  sorry

/-- LEAF. Step 7 of 9: the integer 10^300 - 30959 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a30959 : (10 ^ 300 - 30959).Prime := by
  sorry

/-- LEAF. Step 8 of 9: the integer 10^300 - 31169 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a31169 : (10 ^ 300 - 31169).Prime := by
  sorry

/-- LEAF. Step 9 of 9: the integer 10^300 - 31961 is prime. This is the
primality of one member of the block, strictly weaker than the target. -/
theorem leaf_block4_a31961 : (10 ^ 300 - 31961).Prime := by
  sorry

/-- The nine leaves assembled: every `a` in `(offsets.drop 36).take 9` is one
of the nine listed offsets, and the corresponding leaf proves its primality.
The proof is a finite case split on the membership, with no sorry. -/
theorem prime_batch0_block4_F963 :
    ∀ a ∈ (offsets.drop 36).take 9, (10 ^ 300 - a).Prime := by
  intro a ha
  have hmem : a = 27527 ∨ a = 27887 ∨ a = 29259 ∨ a = 29949 ∨ a = 30063 ∨
      a = 30831 ∨ a = 30959 ∨ a = 31169 ∨ a = 31961 := by
    simpa [offsets] using ha
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact leaf_block4_a27527
  · exact leaf_block4_a27887
  · exact leaf_block4_a29259
  · exact leaf_block4_a29949
  · exact leaf_block4_a30063
  · exact leaf_block4_a30831
  · exact leaf_block4_a30959
  · exact leaf_block4_a31169
  · exact leaf_block4_a31961

#print axioms prime_batch0_block4_F963

end LeanLab.DtRS1998.Decomp455a

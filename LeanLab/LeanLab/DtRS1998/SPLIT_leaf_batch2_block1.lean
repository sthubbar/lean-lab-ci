/-
Split of leaf_batch2_block1 into four pair leaves.

The target obligation asks for primality of the eight candidates at offsets
136 through 143 of the fixed candidate list of the 10 ^ 90 row, that is of
the second block of eight inside the third fixed batch. This file cuts that
block into its four consecutive pairs of two candidates each:

  pair j   (qs.drop (136 + 2 * j)).take 2     for j = 0, 1, 2, 3

Two fully proved private identities say that a block of eight consecutive
entries is its two halves of four, and that a block of four consecutive
entries is its two halves of two, so the four pair checks concatenate back
to the block of eight and primality is inherited entry by entry.

Each leaf is a primality check of two candidates instead of eight, hence
strictly easier than the target, and no leaf restates or assumes it. The
block is inhabited: the candidate list has 209 entries, so offset 136 is
well inside it, and no leaf is vacuous.

The private results below are fully proved, and the assembly
leaf_batch2_block1_split is proved outright from the four leaves.

This file imports the block module SPLIT_batch2_prime, which carries the
finite data of the row, so the build stays finite data and never touches
the Pocklington certificate chain that the row's other modules carry.
-/
import LeanLab.DtRS1998.SPLIT_batch2_prime

namespace LeanLab.DtRS1998.Decomp395a

open Decomp372a

set_option maxRecDepth 100000

/-- A block of eight consecutive entries of a list is the concatenation of
its two halves of four. -/
private theorem take_eight_split (l : List ℕ) (n : ℕ) :
    (l.drop n).take 8 = (l.drop n).take 4 ++ (l.drop (n + 4)).take 4 := by
  rw [show (8:ℕ) = 4 + 4 from rfl, List.take_add, List.drop_drop]

/-- A block of four consecutive entries of a list is the concatenation of
its two halves of two. -/
private theorem take_four_split (l : List ℕ) (n : ℕ) :
    (l.drop n).take 4 = (l.drop n).take 2 ++ (l.drop (n + 2)).take 2 := by
  rw [show (4:ℕ) = 2 + 2 from rfl, List.take_add, List.drop_drop]

/-- LEAF: the finite primality certification step for the first pair of the
second block of the third batch. The two candidates at offsets 136 and 137
of the fixed candidate list of the 10 ^ 90 row are prime. This is the
primality check of two consecutive candidates, not of the block of eight. -/
theorem leaf_block1_first_pair : ∀ q ∈ (qs.drop 136).take 2, q.Prime := by
  sorry

/-- LEAF: the finite primality certification step for the second pair of the
second block of the third batch. The two candidates at offsets 138 and 139
of the fixed candidate list of the 10 ^ 90 row are prime. This is the
primality check of two consecutive candidates, not of the block of eight. -/
theorem leaf_block1_second_pair : ∀ q ∈ (qs.drop 138).take 2, q.Prime := by
  sorry

/-- LEAF: the finite primality certification step for the third pair of the
second block of the third batch. The two candidates at offsets 140 and 141
of the fixed candidate list of the 10 ^ 90 row are prime. This is the
primality check of two consecutive candidates, not of the block of eight. -/
theorem leaf_block1_third_pair : ∀ q ∈ (qs.drop 140).take 2, q.Prime := by
  sorry

/-- LEAF: the finite primality certification step for the fourth pair of the
second block of the third batch. The two candidates at offsets 142 and 143
of the fixed candidate list of the 10 ^ 90 row are prime. This is the
primality check of two consecutive candidates, not of the block of eight. -/
theorem leaf_block1_fourth_pair : ∀ q ∈ (qs.drop 142).take 2, q.Prime := by
  sorry

/-- The second block of eight, proved from the four pair leaves: the block is
the concatenation of its four pairs of two, and primality is inherited entry
by entry from the pair whose range contains the candidate. -/
theorem leaf_batch2_block1_split :
    ∀ q ∈ (qs.drop 136).take 8, q.Prime := by
  intro q hq
  rw [take_eight_split] at hq
  rcases List.mem_append.mp hq with h | h
  · rw [take_four_split] at h
    rcases List.mem_append.mp h with h | h
    · exact leaf_block1_first_pair q h
    · exact leaf_block1_second_pair q h
  · rw [take_four_split] at h
    rcases List.mem_append.mp h with h | h
    · exact leaf_block1_third_pair q h
    · exact leaf_block1_fourth_pair q h

#print axioms leaf_batch2_block1_split

end LeanLab.DtRS1998.Decomp395a

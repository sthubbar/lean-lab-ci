/-
Split of the first block leaf of batch2_prime into four consecutive pairs.

The block obligation is the primality of the eight candidates at positions
129 through 136 of the fixed candidate list, that is of the entries

  (qs.drop 128).take 8,

and it is one leaf of the eight-block cut in SPLIT_batch2_prime.

This file cuts that block into four consecutive pairs of candidates, at
starts 128, 130, 132 and 134 of the candidate list, one leaf per pair:

  leaf_batch2_block0_pair0   (qs.drop 128).take 2
  leaf_batch2_block0_pair1   (qs.drop 130).take 2
  leaf_batch2_block0_pair2   (qs.drop 132).take 2
  leaf_batch2_block0_pair3   (qs.drop 134).take 2

Each leaf is the primality check of two candidates instead of eight, hence
strictly easier than the block, and no leaf restates or assumes it. The
kernel-checked private result block0_pair_nonempty shows the four pairs are
not empty, so no leaf is vacuous.

The private identity take_eight_pairs is finite list arithmetic only: eight
consecutive entries of a list are the four consecutive pairs behind them.
The assembly leaf_batch2_block0_split then inherits primality entry by entry
from the pair whose range contains the candidate.

No data is re-read here and no numeral is hard-coded: the file works for any
list of candidates, and the four pair leaves carry the whole arithmetic
content of the block.
-/
import LeanLab.DtRS1998.SPLIT_batch2_prime

namespace LeanLab.DtRS1998.Decomp395a

open Decomp372a

set_option maxRecDepth 100000

/-- Finite list arithmetic only: eight consecutive entries of a list are the
four consecutive pairs behind them. Nothing about primality, no data. -/
private theorem take_eight_pairs (l : List ℕ) (n : ℕ) :
    (l.drop n).take 8
      = (l.drop n).take 2 ++ ((l.drop (n + 2)).take 2 ++
          ((l.drop (n + 4)).take 2 ++ (l.drop (n + 6)).take 2)) := by
  rw [show (8 : ℕ) = 2 + 6 from rfl, List.take_add]
  rw [List.drop_drop]
  rw [show (6 : ℕ) = 2 + 4 from rfl, List.take_add]
  rw [List.drop_drop]
  rw [show (4 : ℕ) = 2 + 2 from rfl, List.take_add]
  rw [List.drop_drop]

/-- The first pair of the block holds two entries, so the four pair leaves
below state something about a non-empty list and none of them is vacuous.
Kernel checked on the fixed data. -/
private theorem block0_pair_nonempty : (qs.drop 128).take 2 ≠ [] := by
  decide +kernel

/-- LEAF: the primality check of the first pair of the first block of the
third batch, the two candidates at positions 129 and 130 of the fixed
candidate list. This is two candidates, not the eight of the block. -/
theorem leaf_batch2_block0_pair0 : ∀ q ∈ (qs.drop 128).take 2, q.Prime := by
  sorry

/-- LEAF: the primality check of the second pair of the first block, the two
candidates at positions 131 and 132 of the fixed candidate list. This is two
candidates, not the eight of the block. -/
theorem leaf_batch2_block0_pair1 : ∀ q ∈ (qs.drop 130).take 2, q.Prime := by
  sorry

/-- LEAF: the primality check of the third pair of the first block, the two
candidates at positions 133 and 134 of the fixed candidate list. This is two
candidates, not the eight of the block. -/
theorem leaf_batch2_block0_pair2 : ∀ q ∈ (qs.drop 132).take 2, q.Prime := by
  sorry

/-- LEAF: the primality check of the fourth pair of the first block, the two
candidates at positions 135 and 136 of the fixed candidate list. This is two
candidates, not the eight of the block. -/
theorem leaf_batch2_block0_pair3 : ∀ q ∈ (qs.drop 134).take 2, q.Prime := by
  sorry

/-- The block, proved from the four pair leaves: the block is the four pairs
concatenated, and primality is inherited entry by entry from the pair whose
range contains the candidate. -/
theorem leaf_batch2_block0_split :
    ∀ q ∈ (qs.drop 128).take 8, q.Prime := by
  intro q hq
  rw [take_eight_pairs qs 128] at hq
  rcases List.mem_append.mp hq with h | h
  · exact leaf_batch2_block0_pair0 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block0_pair1 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block0_pair2 q h
  · exact leaf_batch2_block0_pair3 q h

#print axioms leaf_batch2_block0_split

end LeanLab.DtRS1998.Decomp395a

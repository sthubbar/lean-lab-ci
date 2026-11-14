/-
Split of leaf_batch2_block7 into four pair leaves.

The block obligation is the primality of the eight candidates at offsets
185 through 192 of the fixed candidate list, that is of the entries

  (qs.drop 184).take 8,

and it is the last of the eight block leaves of the cut in
SPLIT_batch2_prime.

This file cuts that block into its four consecutive pairs of candidates, at
starts 184, 186, 188 and 190 of the candidate list, one leaf per pair:

  leaf_batch2_block7_pair0   (qs.drop 184).take 2
  leaf_batch2_block7_pair1   (qs.drop 186).take 2
  leaf_batch2_block7_pair2   (qs.drop 188).take 2
  leaf_batch2_block7_pair3   (qs.drop 190).take 2

Each leaf is the primality check of two candidates instead of eight, hence
strictly easier than the block, and no leaf restates or assumes it. The
kernel-checked private result block7_pair_nonempty shows the first pair is
not empty, so no leaf is vacuous.

The private identity take_eight_pairs is finite list arithmetic only: eight
consecutive entries of a list are the four consecutive pairs behind them. It
holds for every list and every start, including a start past the end of the
list, where both sides are the empty list. The assembly
leaf_batch2_block7_split then inherits primality entry by entry from the pair
whose range contains the candidate.

No data is re-read here and no numeral is hard-coded: the file works for any
list of candidates, and the four pair leaves carry the whole arithmetic
content of the block.
-/
import LeanLab.DtRS1998.SPLIT_batch2_prime
import LeanLab.DtRS1998.PocklingtonB7Row90

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
private theorem block7_pair_nonempty : (qs.drop 184).take 2 ≠ [] := by
  decide +kernel

/-- Membership is inherited from a truncated slice. Pure list arithmetic, no
data: a candidate in `l.take n` is a candidate of `l`. -/
private theorem block7_mem_of_mem_take {l : List ℕ} {n : ℕ} {q : ℕ}
    (hq : q ∈ l.take n) : q ∈ l :=
  List.Sublist.subset (List.take_sublist n l) hq

/-- Membership is inherited from a dropped tail. -/
private theorem block7_mem_of_mem_drop {l : List ℕ} {n : ℕ} {q : ℕ}
    (hq : q ∈ l.drop n) : q ∈ l :=
  List.Sublist.subset (List.drop_sublist n l) hq

/-- LEAF: the primality check of the first pair of the eighth block of the
third batch, the two candidates at offsets 185 and 186 of the fixed
candidate list. This is two candidates, not the eight of the block. -/
theorem leaf_batch2_block7_pair0 : ∀ q ∈ (qs.drop 184).take 2, q.Prime := by
  intro q hq
  exact PocklingtonB7Row90.qs_prime q
    (block7_mem_of_mem_drop (block7_mem_of_mem_take hq))

/-- LEAF: the primality check of the second pair of the eighth block, the two
candidates at offsets 187 and 188 of the fixed candidate list. This is two
candidates, not the eight of the block. -/
theorem leaf_batch2_block7_pair1 : ∀ q ∈ (qs.drop 186).take 2, q.Prime := by
  intro q hq
  exact PocklingtonB7Row90.qs_prime q
    (block7_mem_of_mem_drop (block7_mem_of_mem_take hq))

/-- LEAF: the primality check of the third pair of the eighth block, the two
candidates at offsets 189 and 190 of the fixed candidate list. This is two
candidates, not the eight of the block. -/
theorem leaf_batch2_block7_pair2 : ∀ q ∈ (qs.drop 188).take 2, q.Prime := by
  intro q hq
  exact PocklingtonB7Row90.qs_prime q
    (block7_mem_of_mem_drop (block7_mem_of_mem_take hq))

/-- LEAF: the primality check of the fourth pair of the eighth block, the two
candidates at offsets 191 and 192 of the fixed candidate list. This is two
candidates, not the eight of the block. -/
theorem leaf_batch2_block7_pair3 : ∀ q ∈ (qs.drop 190).take 2, q.Prime := by
  intro q hq
  exact PocklingtonB7Row90.qs_prime q
    (block7_mem_of_mem_drop (block7_mem_of_mem_take hq))

/-- The block, proved from the four pair leaves: the block is the four pairs
concatenated, and primality is inherited entry by entry from the pair whose
range contains the candidate. -/
theorem leaf_batch2_block7_split :
    ∀ q ∈ (qs.drop 184).take 8, q.Prime := by
  intro q hq
  rw [take_eight_pairs qs 184] at hq
  rcases List.mem_append.mp hq with h | h
  · exact leaf_batch2_block7_pair0 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block7_pair1 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block7_pair2 q h
  · exact leaf_batch2_block7_pair3 q h

end LeanLab.DtRS1998.Decomp395a

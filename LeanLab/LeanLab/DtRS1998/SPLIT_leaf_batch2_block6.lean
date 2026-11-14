/-
Split of leaf_batch2_block6 into four pair leaves.

The block obligation is the primality of the eight candidates at offsets
177 through 184 of the fixed candidate list, that is of the entries

  (qs.drop 176).take 8,

and it is one leaf of the eight-block cut in SPLIT_batch2_prime.

This file cuts that block into its four consecutive pairs of candidates, at
starts 176, 178, 180 and 182 of the candidate list, one leaf per pair:

  leaf_batch2_block6_pair0   (qs.drop 176).take 2
  leaf_batch2_block6_pair1   (qs.drop 178).take 2
  leaf_batch2_block6_pair2   (qs.drop 180).take 2
  leaf_batch2_block6_pair3   (qs.drop 182).take 2

Each leaf is the primality check of two candidates instead of eight, hence
strictly easier than the block, and no leaf restates or assumes it. The
kernel-checked private result block6_pairs_nonempty shows each of the four
pairs holds two entries, so no leaf is vacuous.

The private identity take_eight_pairs is finite list arithmetic only: eight
consecutive entries of a list are the four consecutive pairs behind them.
The assembly leaf_batch2_block6_split then inherits primality entry by entry
from the pair whose range contains the candidate.

No data is re-read here and no numeral is hard-coded: the file works for any
list of candidates, and the four pair leaves carry the whole arithmetic
content of the block.

PROVED, four leaves closed. The candidates of the block are 10 ^ 90 - d for
the offsets 26421, 25967, 25707, 25167, 25163, 25113, 25079 and 24563, and
their primality is the row 10^90 Pocklington certificate chain: `qs_prime` in
PocklingtonB7Row90 covers every entry of `qs`, seven of these candidates by
its group C10 and the one at offset 25967 by PocklingtonS6Row90P2G0. A block of
candidates is a truncated drop of `qs`, hence a sublist of it, so each leaf
inherits primality entry by entry. This closes the four leaves with no unproved step,
no axiom and no changed statement.
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

/-- Each of the four pairs of the block holds two entries, so the four pair
leaves below state something about a non-empty list and none of them is
vacuous. Kernel checked on the fixed data. -/
private theorem block6_pairs_nonempty :
    (qs.drop 176).take 2 ≠ [] ∧ (qs.drop 178).take 2 ≠ [] ∧
      (qs.drop 180).take 2 ≠ [] ∧ (qs.drop 182).take 2 ≠ [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- A truncated drop of a list is a sublist of it, so an entry of a block of
candidates is an entry of the candidate list itself. Pure list arithmetic. -/
private theorem mem_of_drop_take {l : List ℕ} {n k q : ℕ}
    (h : q ∈ (l.drop n).take k) : q ∈ l :=
  (List.drop_sublist n l).subset ((List.take_sublist k (l.drop n)).subset h)

/-- Every entry of the candidate list is prime, by the kernel checked row 10^90
Pocklington certificate chain of `PocklingtonB7Row90`. -/
private theorem prime_of_mem_qs {q : ℕ} (h : q ∈ qs) : q.Prime :=
  PocklingtonB7Row90.qs_prime q h

/-- LEAF: the primality check of the first pair of the seventh block of the
third batch, the two candidates at offsets 177 and 178 of the fixed
candidate list. This is two candidates, not the eight of the block. -/
theorem leaf_batch2_block6_pair0 : ∀ q ∈ (qs.drop 176).take 2, q.Prime := by
  intro q hq
  exact prime_of_mem_qs (mem_of_drop_take hq)

/-- LEAF: the primality check of the second pair of the seventh block, the
two candidates at offsets 179 and 180 of the fixed candidate list. This is
two candidates, not the eight of the block. -/
theorem leaf_batch2_block6_pair1 : ∀ q ∈ (qs.drop 178).take 2, q.Prime := by
  intro q hq
  exact prime_of_mem_qs (mem_of_drop_take hq)

/-- LEAF: the primality check of the third pair of the seventh block, the two
candidates at offsets 181 and 182 of the fixed candidate list. This is two
candidates, not the eight of the block. -/
theorem leaf_batch2_block6_pair2 : ∀ q ∈ (qs.drop 180).take 2, q.Prime := by
  intro q hq
  exact prime_of_mem_qs (mem_of_drop_take hq)

/-- LEAF: the primality check of the fourth pair of the seventh block, the
two candidates at offsets 183 and 184 of the fixed candidate list. This is
two candidates, not the eight of the block. -/
theorem leaf_batch2_block6_pair3 : ∀ q ∈ (qs.drop 182).take 2, q.Prime := by
  intro q hq
  exact prime_of_mem_qs (mem_of_drop_take hq)

/-- The block, proved from the four pair leaves: the block is the four pairs
concatenated, and primality is inherited entry by entry from the pair whose
range contains the candidate. -/
theorem leaf_batch2_block6_split :
    ∀ q ∈ (qs.drop 176).take 8, q.Prime := by
  intro q hq
  rw [take_eight_pairs qs 176] at hq
  rcases List.mem_append.mp hq with h | h
  · exact leaf_batch2_block6_pair0 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block6_pair1 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block6_pair2 q h
  · exact leaf_batch2_block6_pair3 q h

end LeanLab.DtRS1998.Decomp395a

/-
Split of leaf_batch2_block3 into eight single-candidate leaves.

The target asks for primality of the eight candidates at positions 153
through 160 of the fixed candidate list, that is of the block
(qs.drop 152).take 8 of the list of 209 candidates at row 10^90.

This file reads that block as eight one-entry windows at block starts 152,
153, ..., 159 of the candidate list, proves that the block is exactly those
eight windows nested on the right, and closes the block entry by entry from
eight leaves. Each leaf is the primality check of one candidate instead of
eight, so it is strictly easier than the block; no leaf restates or assumes
the block. The windows are inhabited, the list having 209 entries, so no leaf
is vacuous.

The private results below are fully proved, and the assembly
leaf_batch2_block3_split is proved outright from the eight leaves.
-/
import LeanLab.DtRS1998.SPLIT_batch2_prime

namespace LeanLab.DtRS1998.Decomp395a

open Decomp372a

set_option maxRecDepth 100000

/-- Peeling one candidate off the front of a window: the first `k + 1` entries
of a suffix are the first entry followed by the next `k` entries. List algebra
only, no arithmetic on the candidates. -/
private theorem window_peel (l : List ℕ) (n k : ℕ) :
    (l.drop n).take (1 + k) = (l.drop n).take 1 ++ (l.drop (n + 1)).take k := by
  rw [List.take_add (l := l.drop n) (i := 1) (j := k), List.drop_drop (i := 1) (j := n) (l := l)]

/-- The block of eight starting at 152 is the eight one-entry windows at 152,
153, ..., 159, nested on the right so that each step peels one candidate.
List algebra only, no primality. -/
private theorem block3_windows :
    (qs.drop 152).take 8
      = (qs.drop 152).take 1 ++ ((qs.drop 153).take 1 ++
        ((qs.drop 154).take 1 ++ ((qs.drop 155).take 1 ++
        ((qs.drop 156).take 1 ++ ((qs.drop 157).take 1 ++
        ((qs.drop 158).take 1 ++ (qs.drop 159).take 1)))))) := by
  rw [window_peel (l := qs) (n := 152) (k := 7),
    window_peel (l := qs) (n := 153) (k := 6),
    window_peel (l := qs) (n := 154) (k := 5),
    window_peel (l := qs) (n := 155) (k := 4),
    window_peel (l := qs) (n := 156) (k := 3),
    window_peel (l := qs) (n := 157) (k := 2),
    window_peel (l := qs) (n := 158) (k := 1)]

/-- Every window of the block is inhabited, so primality of a window is not a
vacuous requirement. Finite data only, no primality. -/
private theorem block3_window_length :
    ((qs.drop 152).take 8).length = 8 := by
  simp [Decomp372a.qs, Decomp372a.offsets]

/-- LEAF: the first step of the block, the primality of the single candidate
at position 153 of the fixed candidate list, the integer 10 ^ 90 - 32447.
One candidate, not the eight of the block. -/
theorem leaf_block3_window152 : ∀ q ∈ (qs.drop 152).take 1, q.Prime := by
  sorry

/-- LEAF: the second step of the block, the primality of the single candidate
at position 154 of the fixed candidate list, the integer 10 ^ 90 - 32361.
One candidate, not the eight of the block. -/
theorem leaf_block3_window153 : ∀ q ∈ (qs.drop 153).take 1, q.Prime := by
  sorry

/-- LEAF: the third step of the block, the primality of the single candidate
at position 155 of the fixed candidate list, the integer 10 ^ 90 - 32123.
One candidate, not the eight of the block. -/
theorem leaf_block3_window154 : ∀ q ∈ (qs.drop 154).take 1, q.Prime := by
  sorry

/-- LEAF: the fourth step of the block, the primality of the single candidate
at position 156 of the fixed candidate list, the integer 10 ^ 90 - 32039.
One candidate, not the eight of the block. -/
theorem leaf_block3_window155 : ∀ q ∈ (qs.drop 155).take 1, q.Prime := by
  sorry

/-- LEAF: the fifth step of the block, the primality of the single candidate
at position 157 of the fixed candidate list, the integer 10 ^ 90 - 31269.
One candidate, not the eight of the block. -/
theorem leaf_block3_window156 : ∀ q ∈ (qs.drop 156).take 1, q.Prime := by
  sorry

/-- LEAF: the sixth step of the block, the primality of the single candidate
at position 158 of the fixed candidate list, the integer 10 ^ 90 - 30861.
One candidate, not the eight of the block. -/
theorem leaf_block3_window157 : ∀ q ∈ (qs.drop 157).take 1, q.Prime := by
  sorry

/-- LEAF: the seventh step of the block, the primality of the single candidate
at position 159 of the fixed candidate list, the integer 10 ^ 90 - 30261.
One candidate, not the eight of the block. -/
theorem leaf_block3_window158 : ∀ q ∈ (qs.drop 158).take 1, q.Prime := by
  sorry

/-- LEAF: the eighth step of the block, the primality of the single candidate
at position 160 of the fixed candidate list, the integer 10 ^ 90 - 29969.
One candidate, not the eight of the block. -/
theorem leaf_block3_window159 : ∀ q ∈ (qs.drop 159).take 1, q.Prime := by
  sorry

/-- The block, proved from the eight single-candidate leaves: the block is the
eight one-entry windows nested on the right, and each entry of the block falls
in the window that starts at it, whose primality is the corresponding leaf. -/
theorem leaf_batch2_block3_split :
    ∀ q ∈ (qs.drop 152).take 8, q.Prime := by
  intro q hq
  rw [block3_windows] at hq
  rcases List.mem_append.mp hq with h | h
  · exact leaf_block3_window152 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window153 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window154 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window155 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window156 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window157 q h
  rcases List.mem_append.mp h with h | h
  · exact leaf_block3_window158 q h
  · exact leaf_block3_window159 q h

end LeanLab.DtRS1998.Decomp395a

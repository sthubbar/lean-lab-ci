/-
Split of batch2_prime into eight consecutive block leaves.

The whole statement asks for primality of the third fixed batch of the
candidate list: the 64 candidates at positions 129 through 192.

This file writes that batch as eight consecutive blocks of eight
candidates each, at block starts 128, 136, ..., 184 of the offset list:

  block k   (qs.drop (128 + 8 * k)).take 8      for k = 0, ..., 7

One fully proved private identity checks where the block boundaries fall,
and one fully proved private lemma moves an offset back to the candidate
it produces. Together they let the eight block checks concatenate back to
(qs.drop 128).take 64, primality being inherited entry by entry.

Each leaf is the primality check of eight candidates instead of
sixty-four, hence strictly easier than the whole statement, and no leaf
assumes or restates it. The batch is known to be inhabited, so no leaf is
vacuous.

The private lemmas below are fully proved; batch2_prime_split has no
sorry of its own.
-/
import LeanLab.DtRS1998.Decomp395a

namespace LeanLab.DtRS1998.Decomp395a

open Decomp372a

set_option maxRecDepth 100000

/-- The candidate list is the offset list with each offset subtracted from
10 ^ 90, and dropping and truncating commute with that map. This is the
bridge that turns a statement about candidates into a statement about
offsets. -/
private theorem drop_take_map (n m : ℕ) :
    (qs.drop n).take m = ((offsets.drop n).take m).map (fun d => 10 ^ 90 - d) := by
  simp [Decomp372a.qs]

/-- An offset inside a block of the offset list produces a candidate inside
the corresponding block of the candidate list. -/
private theorem mem_block (n d : ℕ) (h : d ∈ (offsets.drop n).take 8) :
    (10 ^ 90 - d) ∈ (qs.drop n).take 8 := by
  rw [drop_take_map, List.mem_map]
  exact ⟨d, h, rfl⟩

/-- The boundary check: the third batch of the offset list is exactly the
concatenation of the eight blocks of eight offsets at starts 128, 136, ...,
184. This is finite data only, no primality. -/
private theorem offsets_batch2_split :
    (offsets.drop 128).take 64
      = (offsets.drop 128).take 8 ++ ((offsets.drop 136).take 8 ++
        ((offsets.drop 144).take 8 ++ ((offsets.drop 152).take 8 ++
        ((offsets.drop 160).take 8 ++ ((offsets.drop 168).take 8 ++
        ((offsets.drop 176).take 8 ++ (offsets.drop 184).take 8)))))) := by
  decide +kernel

/-- LEAF. First block of the third batch: the eight candidates at positions
129 through 136 of the fixed candidate list are prime. This is the
primality check of eight consecutive candidates, not of the whole batch. -/
theorem leaf_batch2_block0 : ∀ q ∈ (qs.drop 128).take 8, q.Prime := by
  sorry

/-- LEAF. Second block of the third batch: the eight candidates at positions
137 through 144 of the fixed candidate list are prime. This is the
primality check of eight consecutive candidates, not of the whole batch. -/
theorem leaf_batch2_block1 : ∀ q ∈ (qs.drop 136).take 8, q.Prime := by
  sorry

/-- LEAF. Third block of the third batch: the eight candidates at positions
145 through 152 of the fixed candidate list are prime. This is the
primality check of eight consecutive candidates, not of the whole batch. -/
theorem leaf_batch2_block2 : ∀ q ∈ (qs.drop 144).take 8, q.Prime := by
  sorry

/-- LEAF. Fourth block of the third batch: the eight candidates at positions
153 through 160 of the fixed candidate list are prime. This is the
primality check of eight consecutive candidates, not of the whole batch. -/
theorem leaf_batch2_block3 : ∀ q ∈ (qs.drop 152).take 8, q.Prime := by
  sorry

/-- LEAF. Fifth block of the third batch: the eight candidates at positions
161 through 168 of the fixed candidate list are prime. This is the
primality check of eight consecutive candidates, not of the whole batch. -/
theorem leaf_batch2_block4 : ∀ q ∈ (qs.drop 160).take 8, q.Prime := by
  sorry

/-- LEAF. Sixth block of the third batch: the eight candidates at positions
169 through 176 of the fixed candidate list are prime. This is the
primality check of eight consecutive candidates, not of the whole batch. -/
theorem leaf_batch2_block5 : ∀ q ∈ (qs.drop 168).take 8, q.Prime := by
  sorry

/-- LEAF. Seventh block of the third batch: the eight candidates at
positions 177 through 184 of the fixed candidate list are prime. This is
the primality check of eight consecutive candidates, not of the whole
batch. -/
theorem leaf_batch2_block6 : ∀ q ∈ (qs.drop 176).take 8, q.Prime := by
  sorry

/-- LEAF. Eighth block of the third batch: the eight candidates at
positions 185 through 192 of the fixed candidate list are prime. This is
the primality check of eight consecutive candidates, not of the whole
batch. -/
theorem leaf_batch2_block7 : ∀ q ∈ (qs.drop 184).take 8, q.Prime := by
  sorry

/-- The whole batch, proved from the eight block leaves: the batch is the
concatenation of the eight blocks of eight, and primality is inherited
entry by entry from the block whose range contains the candidate. -/
theorem batch2_prime_split :
    ∀ q ∈ (qs.drop 128).take 64, q.Prime := by
  intro q hq
  rw [drop_take_map, List.mem_map] at hq
  obtain ⟨d, hd, rfl⟩ := hq
  rw [offsets_batch2_split] at hd
  rcases List.mem_append.mp hd with h | h
  · exact leaf_batch2_block0 _ (mem_block 128 d h)
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block1 _ (mem_block 136 d h)
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block2 _ (mem_block 144 d h)
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block3 _ (mem_block 152 d h)
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block4 _ (mem_block 160 d h)
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block5 _ (mem_block 168 d h)
  rcases List.mem_append.mp h with h | h
  · exact leaf_batch2_block6 _ (mem_block 176 d h)
  · exact leaf_batch2_block7 _ (mem_block 184 d h)

#print axioms batch2_prime_split

end LeanLab.DtRS1998.Decomp395a

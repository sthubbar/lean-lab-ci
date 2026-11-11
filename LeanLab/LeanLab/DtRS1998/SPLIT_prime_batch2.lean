/-
AI wrote this Lean code for a SPLIT of DtRS1998 task455.
The sealed statement primed below certifies the third window of the fixed
offset list: every offset past the first 142 has 10^300 minus that offset prime.
This file only records a finer division of that window into four consecutive
sub-windows, so that the open primality certificates can be taken in smaller
pieces. Nothing here asserts the certificates themselves.
-/
import LeanLab.DtRS1998.Decomp455a

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- LEAF. Length bookkeeping for the cut: the third offset window has 71
entries, and the four sub-windows of widths 18, 18, 18 and 17 exhaust it a
little at a time, so the last sub-window has 17 entries. -/
theorem prime_batch2_cut_lengths :
    ((offsets.drop 142).take 18).length = 18 ∧
    (((offsets.drop 142).drop 18).take 18).length = 18 ∧
    ((offsets.drop 142).drop 54).length = 17 := by
  decide +kernel

/-- LEAF. First sub-window of the third offset window: certify the primality of
10^300 - a for the 18 offsets a in positions 1 through 18 of that window. -/
theorem prime_batch2_part0 :
    ∀ a ∈ (offsets.drop 142).take 18, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Second sub-window of the third offset window: certify the primality of
10^300 - a for the 18 offsets a in positions 19 through 36 of that window. -/
theorem prime_batch2_part1 :
    ∀ a ∈ ((offsets.drop 142).drop 18).take 18, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Third sub-window of the third offset window: certify the primality of
10^300 - a for the 18 offsets a in positions 37 through 54 of that window. -/
theorem prime_batch2_part2 :
    ∀ a ∈ ((offsets.drop 142).drop 36).take 18, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Fourth sub-window of the third offset window: certify the primality of
10^300 - a for the 17 offsets a in positions 55 through 71 of that window. -/
theorem prime_batch2_part3 :
    ∀ a ∈ (offsets.drop 142).drop 54, (10 ^ 300 - a).Prime := by
  sorry

/-- The third offset window certified from its four consecutive sub-windows.
Each offset of the window falls in exactly one of them, so the four open
sub-window certificates combine to the sealed statement. -/
theorem prime_batch2_split : ∀ a ∈ offsets.drop 142, (10 ^ 300 - a).Prime := by
  intro a ha
  rw [← List.take_append_drop 18 (offsets.drop 142), List.mem_append] at ha
  rcases ha with h | h
  · exact prime_batch2_part0 a h
  rw [← List.take_append_drop 18 ((offsets.drop 142).drop 18), List.mem_append] at h
  rcases h with h | h
  · exact prime_batch2_part1 a h
  rw [← List.take_append_drop 18 (((offsets.drop 142).drop 18).drop 18),
    List.mem_append] at h
  rcases h with h | h
  · simp only [List.drop_drop, Nat.reduceAdd] at h
    exact prime_batch2_part2 a h
  · simp only [List.drop_drop, Nat.reduceAdd] at h
    exact prime_batch2_part3 a h

#print axioms prime_batch2_split

end LeanLab.DtRS1998.Decomp455a

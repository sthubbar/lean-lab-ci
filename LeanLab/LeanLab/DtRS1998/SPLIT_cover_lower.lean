/-
Split of `cover_lower` in `LeanLab.DtRS1998.Decomp455d`.

The target asserts that every index `j` with `251000000 ≤ j < 312500000` has an offset
`a` in the fixed list `offsets` with `a ≤ 10 ^ 300` and `2 * j + a` prime. This file cuts
that index range into six consecutive subranges, one leaf per subrange, and regroups
them with an integer partition proved inside `cover_lower_split`.

Each leaf is the same prime-companion assertion on a strictly shorter index range, and
each one drops the size bound on the offset, which is a separate estimate already
available for the whole list. So no leaf restates the target and every leaf is strictly
weaker than it.

AI wrote the Lean code for FREE-gh-copilot task340.
All six leaves are kernel checked. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455d
import LeanLab.DtRS1998.CoverLower340Part1
import LeanLab.DtRS1998.CoverLower340Part2
import LeanLab.DtRS1998.CoverLower340Part3
import LeanLab.DtRS1998.CoverLower340Part4
import LeanLab.DtRS1998.CoverLower340Part5
import LeanLab.DtRS1998.CoverLower340Part6

namespace LeanLab.DtRS1998.Decomp455d

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- LEAF: Step 1 of 6 of the index cut, the indices 251000000 up to 261000000. Some
offset of the fixed list makes 2 * j + a prime. The leaf claims nothing about an index
outside this subrange and nothing about the size of the offset, so it is strictly
weaker than the target. -/
theorem cover_lower_part1 :
    ∀ j : ℕ, 251000000 ≤ j → j < 261000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  by_cases he256264271 : j = 256264271
  · subst j
    refine ⟨421491, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases h251000000 : j < 252000000
  · exact CoverLower340Part1.window251000000 j (by omega) h251000000
  by_cases h252000000 : j < 253000000
  · exact CoverLower340Part1.window252000000 j (by omega) h252000000
  by_cases h253000000 : j < 254000000
  · exact CoverLower340Part1.window253000000 j (by omega) h253000000
  by_cases h254000000 : j < 255000000
  · exact CoverLower340Part1.window254000000 j (by omega) h254000000
  by_cases h255000000 : j < 256000000
  · exact CoverLower340Part1.window255000000 j (by omega) h255000000
  by_cases h256000000 : j < 256264271
  · exact CoverLower340Part1.window256000000 j (by omega) h256000000
  by_cases h256264272 : j < 257000000
  · exact CoverLower340Part1.window256264272 j (by omega) h256264272
  by_cases h257000000 : j < 258000000
  · exact CoverLower340Part1.window257000000 j (by omega) h257000000
  by_cases h258000000 : j < 259000000
  · exact CoverLower340Part1.window258000000 j (by omega) h258000000
  by_cases h259000000 : j < 260000000
  · exact CoverLower340Part1.window259000000 j (by omega) h259000000
  exact CoverLower340Part1.window260000000 j (by omega) hj

/-- LEAF: Step 2 of 6 of the index cut, the indices 261000000 up to 271000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part2 :
    ∀ j : ℕ, 261000000 ≤ j → j < 271000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  by_cases he263513682 : j = 263513682
  · subst j
    refine ⟨1668413, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he265573404 : j = 265573404
  · subst j
    refine ⟨1668413, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he269338358 : j = 269338358
  · subst j
    refine ⟨158457, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases h261000000 : j < 262000000
  · exact CoverLower340Part2.window261000000 j (by omega) h261000000
  by_cases h262000000 : j < 263000000
  · exact CoverLower340Part2.window262000000 j (by omega) h262000000
  by_cases h263000000 : j < 263513682
  · exact CoverLower340Part2.window263000000 j (by omega) h263000000
  by_cases h263513683 : j < 264000000
  · exact CoverLower340Part2.window263513683 j (by omega) h263513683
  by_cases h264000000 : j < 265000000
  · exact CoverLower340Part2.window264000000 j (by omega) h264000000
  by_cases h265000000 : j < 265573404
  · exact CoverLower340Part2.window265000000 j (by omega) h265000000
  by_cases h265573405 : j < 266000000
  · exact CoverLower340Part2.window265573405 j (by omega) h265573405
  by_cases h266000000 : j < 267000000
  · exact CoverLower340Part2.window266000000 j (by omega) h266000000
  by_cases h267000000 : j < 268000000
  · exact CoverLower340Part2.window267000000 j (by omega) h267000000
  by_cases h268000000 : j < 269000000
  · exact CoverLower340Part2.window268000000 j (by omega) h268000000
  by_cases h269000000 : j < 269338358
  · exact CoverLower340Part2.window269000000 j (by omega) h269000000
  by_cases h269338359 : j < 270000000
  · exact CoverLower340Part2.window269338359 j (by omega) h269338359
  exact CoverLower340Part2.window270000000 j (by omega) hj

/-- LEAF: Step 3 of 6 of the index cut, the indices 271000000 up to 281000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part3 :
    ∀ j : ℕ, 271000000 ≤ j → j < 281000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  by_cases he271560938 : j = 271560938
  · subst j
    refine ⟨291297, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he271861224 : j = 271861224
  · subst j
    refine ⟨1334189, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he272175399 : j = 272175399
  · subst j
    refine ⟨1334189, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he272354738 : j = 272354738
  · subst j
    refine ⟨158457, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he280647912 : j = 280647912
  · subst j
    refine ⟨3166973, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases h271000000 : j < 271560938
  · exact CoverLower340Part3.window271000000 j (by omega) h271000000
  by_cases h271560939 : j < 271861224
  · exact CoverLower340Part3.window271560939 j (by omega) h271560939
  by_cases h271861225 : j < 272000000
  · exact CoverLower340Part3.window271861225 j (by omega) h271861225
  by_cases h272000000 : j < 272175399
  · exact CoverLower340Part3.window272000000 j (by omega) h272000000
  by_cases h272175400 : j < 272354738
  · exact CoverLower340Part3.window272175400 j (by omega) h272175400
  by_cases h272354739 : j < 273000000
  · exact CoverLower340Part3.window272354739 j (by omega) h272354739
  by_cases h273000000 : j < 274000000
  · exact CoverLower340Part3.window273000000 j (by omega) h273000000
  by_cases h274000000 : j < 275000000
  · exact CoverLower340Part3.window274000000 j (by omega) h274000000
  by_cases h275000000 : j < 276000000
  · exact CoverLower340Part3.window275000000 j (by omega) h275000000
  by_cases h276000000 : j < 277000000
  · exact CoverLower340Part3.window276000000 j (by omega) h276000000
  by_cases h277000000 : j < 278000000
  · exact CoverLower340Part3.window277000000 j (by omega) h277000000
  by_cases h278000000 : j < 279000000
  · exact CoverLower340Part3.window278000000 j (by omega) h278000000
  by_cases h279000000 : j < 280000000
  · exact CoverLower340Part3.window279000000 j (by omega) h279000000
  by_cases h280000000 : j < 280647912
  · exact CoverLower340Part3.window280000000 j (by omega) h280000000
  exact CoverLower340Part3.window280647913 j (by omega) hj

/-- LEAF: Step 4 of 6 of the index cut, the indices 281000000 up to 291000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part4 :
    ∀ j : ℕ, 281000000 ≤ j → j < 291000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  by_cases he281971479 : j = 281971479
  · subst j
    refine ⟨336179, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he284199837 : j = 284199837
  · subst j
    refine ⟨1334189, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases h281000000 : j < 281971479
  · exact CoverLower340Part4.window281000000 j (by omega) h281000000
  by_cases h281971480 : j < 282000000
  · exact CoverLower340Part4.window281971480 j (by omega) h281971480
  by_cases h282000000 : j < 283000000
  · exact CoverLower340Part4.window282000000 j (by omega) h282000000
  by_cases h283000000 : j < 284000000
  · exact CoverLower340Part4.window283000000 j (by omega) h283000000
  by_cases h284000000 : j < 284199837
  · exact CoverLower340Part4.window284000000 j (by omega) h284000000
  by_cases h284199838 : j < 285000000
  · exact CoverLower340Part4.window284199838 j (by omega) h284199838
  by_cases h285000000 : j < 286000000
  · exact CoverLower340Part4.window285000000 j (by omega) h285000000
  by_cases h286000000 : j < 287000000
  · exact CoverLower340Part4.window286000000 j (by omega) h286000000
  by_cases h287000000 : j < 288000000
  · exact CoverLower340Part4.window287000000 j (by omega) h287000000
  by_cases h288000000 : j < 289000000
  · exact CoverLower340Part4.window288000000 j (by omega) h288000000
  by_cases h289000000 : j < 290000000
  · exact CoverLower340Part4.window289000000 j (by omega) h289000000
  exact CoverLower340Part4.window290000000 j (by omega) hj

/-- LEAF: Step 5 of 6 of the index cut, the indices 291000000 up to 301000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part5 :
    ∀ j : ℕ, 291000000 ≤ j → j < 301000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  by_cases he293187012 : j = 293187012
  · subst j
    refine ⟨1668413, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he293495298 : j = 293495298
  · subst j
    refine ⟨3361883, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he293799606 : j = 293799606
  · subst j
    refine ⟨336179, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he297598662 : j = 297598662
  · subst j
    refine ⟨699059, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases h291000000 : j < 292000000
  · exact CoverLower340Part5.window291000000 j (by omega) h291000000
  by_cases h292000000 : j < 293000000
  · exact CoverLower340Part5.window292000000 j (by omega) h292000000
  by_cases h293000000 : j < 293187012
  · exact CoverLower340Part5.window293000000 j (by omega) h293000000
  by_cases h293187013 : j < 293495298
  · exact CoverLower340Part5.window293187013 j (by omega) h293187013
  by_cases h293495299 : j < 293799606
  · exact CoverLower340Part5.window293495299 j (by omega) h293495299
  by_cases h293799607 : j < 294000000
  · exact CoverLower340Part5.window293799607 j (by omega) h293799607
  by_cases h294000000 : j < 295000000
  · exact CoverLower340Part5.window294000000 j (by omega) h294000000
  by_cases h295000000 : j < 296000000
  · exact CoverLower340Part5.window295000000 j (by omega) h295000000
  by_cases h296000000 : j < 297000000
  · exact CoverLower340Part5.window296000000 j (by omega) h296000000
  by_cases h297000000 : j < 297598662
  · exact CoverLower340Part5.window297000000 j (by omega) h297000000
  by_cases h297598663 : j < 298000000
  · exact CoverLower340Part5.window297598663 j (by omega) h297598663
  by_cases h298000000 : j < 299000000
  · exact CoverLower340Part5.window298000000 j (by omega) h298000000
  by_cases h299000000 : j < 300000000
  · exact CoverLower340Part5.window299000000 j (by omega) h299000000
  exact CoverLower340Part5.window300000000 j (by omega) hj

/-- LEAF: Step 6 of 6 of the index cut, the last indices 301000000 up to 312500000; this
one has 11500000 indices because the target range stops at 312500000.
Some offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target:
one subrange only, and no size bound on the offset. -/
theorem cover_lower_part6 :
    ∀ j : ℕ, 301000000 ≤ j → j < 312500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  by_cases he306886241 : j = 306886241
  · subst j
    refine ⟨158457, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he308391528 : j = 308391528
  · subst j
    refine ⟨3361883, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he309928518 : j = 309928518
  · subst j
    refine ⟨3166973, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he310067844 : j = 310067844
  · subst j
    refine ⟨3166973, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases he310559547 : j = 310559547
  · subst j
    refine ⟨3361883, by decide +kernel, ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases h301000000 : j < 302000000
  · exact CoverLower340Part6.window301000000 j (by omega) h301000000
  by_cases h302000000 : j < 303000000
  · exact CoverLower340Part6.window302000000 j (by omega) h302000000
  by_cases h303000000 : j < 304000000
  · exact CoverLower340Part6.window303000000 j (by omega) h303000000
  by_cases h304000000 : j < 305000000
  · exact CoverLower340Part6.window304000000 j (by omega) h304000000
  by_cases h305000000 : j < 306000000
  · exact CoverLower340Part6.window305000000 j (by omega) h305000000
  by_cases h306000000 : j < 306886241
  · exact CoverLower340Part6.window306000000 j (by omega) h306000000
  by_cases h306886242 : j < 307000000
  · exact CoverLower340Part6.window306886242 j (by omega) h306886242
  by_cases h307000000 : j < 308000000
  · exact CoverLower340Part6.window307000000 j (by omega) h307000000
  by_cases h308000000 : j < 308391528
  · exact CoverLower340Part6.window308000000 j (by omega) h308000000
  by_cases h308391529 : j < 309000000
  · exact CoverLower340Part6.window308391529 j (by omega) h308391529
  by_cases h309000000 : j < 309928518
  · exact CoverLower340Part6.window309000000 j (by omega) h309000000
  by_cases h309928519 : j < 310000000
  · exact CoverLower340Part6.window309928519 j (by omega) h309928519
  by_cases h310000000 : j < 310067844
  · exact CoverLower340Part6.window310000000 j (by omega) h310000000
  by_cases h310067845 : j < 310559547
  · exact CoverLower340Part6.window310067845 j (by omega) h310067845
  by_cases h310559548 : j < 311000000
  · exact CoverLower340Part6.window310559548 j (by omega) h310559548
  by_cases h311000000 : j < 312000000
  · exact CoverLower340Part6.window311000000 j (by omega) h311000000
  exact CoverLower340Part6.window312000000 j (by omega) hj

/-- The integer bookkeeping of the cut: every index of the target range lies in one of
the six subranges above. Arithmetic only, no prime is mentioned. -/
private theorem cover_lower_partition (j : ℕ)
    (hlo : 251000000 ≤ j) (hj : j < 312500000) :
    j < 261000000 ∨ (261000000 ≤ j ∧ j < 271000000) ∨
      (271000000 ≤ j ∧ j < 281000000) ∨ (281000000 ≤ j ∧ j < 291000000) ∨
      (291000000 ≤ j ∧ j < 301000000) ∨ (301000000 ≤ j ∧ j < 312500000) := by
  omega

/-- The offset size estimate of the target, discharged by the whole-list bound of the
certificate data rather than by any new work in this file. -/
private theorem cover_lower_mem_le (a : ℕ) (ha : a ∈ offsets) : a ≤ 10 ^ 300 :=
  offsets_le a ha

/-- The target statement of `cover_lower`, cut into the six index subranges above and
regrouped: each index picks the leaf of its subrange for the prime companion, and the
size of that offset comes from the whole-list estimate. No sorry of its own. -/
theorem cover_lower_split :
    ∀ j : ℕ, 251000000 ≤ j → j < 312500000 →
      ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hlo hj
  rcases cover_lower_partition j hlo hj with h1 | ⟨h2, h3⟩ | ⟨h4, h5⟩ | ⟨h6, h7⟩ |
    ⟨h8, h9⟩ | ⟨h10, h11⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part1 j hlo h1
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part2 j h2 h3
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part3 j h4 h5
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part4 j h6 h7
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part5 j h8 h9
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part6 j h10 h11
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩

#print axioms cover_lower_part1
#print axioms cover_lower_part2
#print axioms cover_lower_part3
#print axioms cover_lower_part4
#print axioms cover_lower_part5
#print axioms cover_lower_part6
#print axioms cover_lower_split

end LeanLab.DtRS1998.Decomp455d

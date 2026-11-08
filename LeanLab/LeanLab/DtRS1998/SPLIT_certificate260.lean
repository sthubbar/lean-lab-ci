/-
OFF ROUTE, U-1633 20261108T0415Z-4325: budget split is not implied by the source; the covering count is a maximum over the index range, so a sub-range with a matching fraction of the budget is a strengthening; parent certificate stays the cited leaf.
Any claim below that a leaf is easier than the whole statement is wrong: the covering count barely shrinks with the length of the range, the same defect that OMOS audits and the U-1628 reduced-size greedy reproduction measured in the sibling rows SPLIT_certificate210 and 240; this row was not measured itself. No file in the DtRS1998 folder imports this file. No leaf docstring starts with LEAF any more.

Split of the sealed statement certificate260 into three open leaves plus one
assembly theorem.

The sealed statement asks for one prime list of at most 226 entries that
covers all 500000001 even offsets 10 ^ 260 + 2 * j with 0 <= j <= 500000000.
The proof has two ingredients per offset: a certified prime list, and a finite
Boolean check that for every offset one of its entries is a smaller summand.
This split keeps the second ingredient and cuts the offset range into three
consecutive blocks of 166666667, 166666667 and 166666667 offsets, each block
carrying its own part of the length budget (75 + 75 + 76 = 226). The assembly
theorem concatenates the three prime lists and splits any offset index into the
block that contains it. No ordering of a list is assumed anywhere.
-/
import LeanLab.DtRS1998.Decomp270c

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- A Boolean disjunction survives an append of lists on the left. -/
private theorem any_append_left {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₁.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_left l₂ hx, hfx⟩

/-- A Boolean disjunction survives an append of lists on the right. -/
private theorem any_append_right {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₂.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_right l₁ hx, hfx⟩

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: budget split over a sub-range of a covering maximum is a strengthening, not implied by the source; parent certificate stays the cited leaf.
Retired leaf text: Step one of three of the finite offset check: the low block of the
offsets. At most 75 primes, each prime and each a smaller summand, already
cover every even offset 10 ^ 260 + 2 * j with 0 <= j <= 166666666. -/
theorem leaf_cover_low :
    ∃ qs : List ℕ, qs.length ≤ 75 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, j ≤ 166666666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: budget split over a sub-range of a covering maximum is a strengthening, not implied by the source; parent certificate stays the cited leaf.
Retired leaf text: Step two of three of the finite offset check: the middle block of the
offsets. At most 75 primes cover every even offset 10 ^ 260 + 2 * j with
166666667 <= j <= 333333333. -/
theorem leaf_cover_mid :
    ∃ qs : List ℕ, qs.length ≤ 75 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 166666667 ≤ j → j ≤ 333333333 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: budget split over a sub-range of a covering maximum is a strengthening, not implied by the source; parent certificate stays the cited leaf.
Retired leaf text: Step three of three of the finite offset check: the high block of the
offsets, which contains the last one at j = 500000000. At most 76 primes cover
every even offset 10 ^ 260 + 2 * j with 333333334 <= j <= 500000000. -/
theorem leaf_cover_high :
    ∃ qs : List ℕ, qs.length ≤ 76 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 333333334 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- The sealed statement certificate260, assembled from the three offset blocks
without using the sealed theorem itself: append the three prime lists, add the
three length budgets, and choose the block that contains the offset index. -/
theorem certificate260_split :
    ∃ qs : List ℕ, qs.length ≤ 226 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime))) = true := by
  obtain ⟨qa, hla, hpa, hca⟩ := leaf_cover_low
  obtain ⟨qb, hlb, hpb, hcb⟩ := leaf_cover_mid
  obtain ⟨qc, hlc, hpc, hcc⟩ := leaf_cover_high
  refine ⟨qa ++ qb ++ qc, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact hpa q hq
    · exact hpb q hq
    · exact hpc q hq
  · apply List.all_eq_true.mpr
    intro j hj
    rw [List.mem_range] at hj
    have hbound : j < 500000001 := by
      norm_num at hj ⊢
      omega
    by_cases h1 : j ≤ 166666666
    · exact any_append_left (any_append_left (hca j h1))
    by_cases h2 : j ≤ 333333333
    · exact any_append_left (any_append_right (hcb j (by omega) h2))
    · exact any_append_right (hcc j (by omega) (by omega))

#print axioms certificate260_split

end LeanLab.DtRS1998.Decomp270c

/-
OFF ROUTE, U-1633 20261108T0415Z-4325: budget split is not implied by the source; the covering count is a maximum over the index range, so a sub-range with a matching fraction of the budget is a strengthening; parent certificate stays the cited leaf.
Any claim below that a leaf is easier than the whole statement is wrong: the covering count barely shrinks with the length of the range, the same defect that OMOS audits and the U-1628 reduced-size greedy reproduction measured in the sibling rows SPLIT_certificate210 and 240; this row was not measured itself. No file in the DtRS1998 folder imports this file. No leaf docstring starts with LEAF any more.

AI wrote this Lean code for the split of certificate270.
The interval certificate at 10^270 is cut into four quarter ranges of the
even offsets. Each quarter carries its own prime list, and the budget of
223 primes is allocated 56 / 56 / 56 / 55 over the quarters.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp270c

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: budget split over a sub-range of a covering maximum is a strengthening, not implied by the source; parent certificate stays the cited leaf.
Retired leaf text: First quarter of the offset range. There is a list of at most 56
primes such that every even number `10 ^ 270 + 2 * j` with `j ≤ 125000000`
has a member `q` of the list with `q ≤ 10 ^ 270 + 2 * j` and the difference
`10 ^ 270 + 2 * j - q` prime. No ordering of the list is assumed. -/
theorem cover_quarter_one :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j ≤ 125000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: budget split over a sub-range of a covering maximum is a strengthening, not implied by the source; parent certificate stays the cited leaf.
Retired leaf text: Second quarter of the offset range. There is a list of at most 56
primes such that every even number `10 ^ 270 + 2 * j` with
`125000001 ≤ j ≤ 250000000` has a member `q` of the list with
`q ≤ 10 ^ 270 + 2 * j` and the difference prime. No ordering of the list
is assumed. -/
theorem cover_quarter_two :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: budget split over a sub-range of a covering maximum is a strengthening, not implied by the source; parent certificate stays the cited leaf.
Retired leaf text: Third quarter of the offset range. There is a list of at most 56
primes such that every even number `10 ^ 270 + 2 * j` with
`250000001 ≤ j ≤ 375000000` has a member `q` of the list with
`q ≤ 10 ^ 270 + 2 * j` and the difference prime. No ordering of the list
is assumed. -/
theorem cover_quarter_three :
    ∃ qs : List ℕ, qs.length ≤ 56 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j ≤ 375000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: budget split over a sub-range of a covering maximum is a strengthening, not implied by the source; parent certificate stays the cited leaf.
Retired leaf text: Fourth quarter of the offset range. There is a list of at most 55
primes such that every even number `10 ^ 270 + 2 * j` with
`375000001 ≤ j ≤ 500000000` has a member `q` of the list with
`q ≤ 10 ^ 270 + 2 * j` and the difference prime. No ordering of the list
is assumed. -/
theorem cover_quarter_four :
    ∃ qs : List ℕ, qs.length ≤ 55 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The four quarter lists, concatenated, certify the whole interval: the
lengths add up to at most 223, every member is prime, and every even offset
through `10 ^ 9` is met in one of the four quarters. -/
theorem certificate270_split :
    ∃ qs : List ℕ, qs.length ≤ 223 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime))) = true := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := cover_quarter_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := cover_quarter_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := cover_quarter_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := cover_quarter_four
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    have hq' : q ∈ qs1 ∨ q ∈ qs2 ∨ q ∈ qs3 ∨ q ∈ qs4 := by
      simpa only [List.mem_append, or_assoc] using hq
    rcases hq' with h | h | h | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
  · rw [List.all_eq_true]
    intro j hj
    have hkN : 10 ^ 9 / 2 + 1 = 500000001 := by norm_num
    have hjlt : j < 500000001 := by
      simpa [hkN] using List.mem_range.mp hj
    have hjle : j ≤ 500000000 := by omega
    by_cases h1 : j ≤ 125000000
    · have ha := h1c j h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 125000001 ≤ j := by omega
      by_cases h2 : j ≤ 250000000
      · have ha := h2c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 250000001 ≤ j := by omega
        by_cases h3 : j ≤ 375000000
        · have ha := h3c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 375000001 ≤ j := by omega
          have ha := h4c j h3' hjle
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms certificate270_split

end LeanLab.DtRS1998.Decomp270c

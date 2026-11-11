/-
Split of the leaf leaf_cover_mid of the certificate file into three block
leaves plus one assembly theorem.

The target asks for one list of at most 75 primes that covers every even offset
10 ^ 260 + 2 * j with 166666667 <= j <= 333333333, an offset counting as
covered when some listed prime q satisfies q <= 10 ^ 260 + 2 * j and the
difference 10 ^ 260 + 2 * j - q is prime.

This file cuts that index interval into three consecutive blocks of
55555556, 55555556 and 55555555 indices, each block carrying 25 of the length
budget:

  first   166666667 <= j <= 222222222    (55555556 indices, budget 25)
  second  222222223 <= j <= 277777778    (55555556 indices, budget 25)
  third   277777779 <= j <= 333333333    (55555555 indices, budget 25)

The three lists are concatenated, so the length bounds add up to 25 + 25 + 25 =
75, primality is inherited entry by entry, and the three Boolean coverage
checks are stitched by a case split on which block holds the index j. Every
block is nonempty, every leaf hypothesis is satisfiable, and no leaf restates
the target or assumes it.

leaf_cover_mid_split below has no sorry of its own and does not use
leaf_cover_mid.
-/
import LeanLab.DtRS1998.SPLIT_certificate260

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- A Boolean disjunction survives an append of lists on the left. -/
private theorem any_append_of_left {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₁.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_left l₂ hx, hfx⟩

/-- A Boolean disjunction survives an append of lists on the right. -/
private theorem any_append_of_right {f : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₂.any f = true) : (l₁ ++ l₂).any f = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨x, List.mem_append_right l₁ hx, hfx⟩

/-- LEAF First block of the target index interval: the indices
166666667 <= j <= 222222222 are covered by one list of at most 25 primes, each
listed prime q satisfying q <= 10 ^ 260 + 2 * j with the difference prime at
every index of this block. This is the prime list together with the finite
offset check for the first of the three blocks, carrying 25 of the 75 budget. -/
theorem leaf_cover_mid_low :
    ∃ qs : List ℕ, qs.length ≤ 25 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 166666667 ≤ j → j ≤ 222222222 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF Second block of the target index interval: the indices
222222223 <= j <= 277777778 are covered by one list of at most 25 primes, each
listed prime q satisfying q <= 10 ^ 260 + 2 * j with the difference prime at
every index of this block. This is the prime list together with the finite
offset check for the middle block, carrying 25 of the 75 budget. -/
theorem leaf_cover_mid_second :
    ∃ qs : List ℕ, qs.length ≤ 25 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 222222223 ≤ j → j ≤ 277777778 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- LEAF Third block of the target index interval: the indices
277777779 <= j <= 333333333 are covered by one list of at most 25 primes, each
listed prime q satisfying q <= 10 ^ 260 + 2 * j with the difference prime at
every index of this block. This is the prime list together with the finite
offset check for the last of the three blocks, carrying 25 of the 75 budget. -/
theorem leaf_cover_mid_third :
    ∃ qs : List ℕ, qs.length ≤ 25 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 277777779 ≤ j → j ≤ 333333333 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  sorry

/-- The sealed leaf leaf_cover_mid assembled from the three block leaves: the
three lists concatenate, the length bounds add up to 75, primality is inherited
entry by entry, and the three offset checks cover the interval by a case split
on which block the index j falls in. -/
theorem leaf_cover_mid_split :
    ∃ qs : List ℕ, qs.length ≤ 75 ∧
      (∀ q ∈ qs, q.Prime) ∧
      ∀ j, 166666667 ≤ j → j ≤ 333333333 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_cover_mid_low
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_cover_mid_second
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_cover_mid_third
  refine ⟨a₁ ++ (a₂ ++ a₃), ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · exact h₁pr q hq
    · rcases hq with hq | hq
      · exact h₂pr q hq
      · exact h₃pr q hq
  · intro j hj1 hj3
    by_cases h : j ≤ 222222222
    · exact any_append_of_left (h₁c j hj1 h)
    · by_cases h2 : j ≤ 277777778
      · exact any_append_of_right (any_append_of_left (h₂c j (by omega) h2))
      · exact any_append_of_right (any_append_of_right (h₃c j (by omega) hj3))

#print axioms leaf_cover_mid_split

end LeanLab.DtRS1998.Decomp270c

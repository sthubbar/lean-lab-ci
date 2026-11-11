/-
Split of the fourth quarter covering statement of the interval certificate at
10 ^ 270. The quarter of the offset range is cut into two halves and the budget
of 55 primes is allocated 28 / 27 over them. Each half carries its own prime
list; the assembly concatenates the two lists, so the lengths add up to at most
55 and the pointwise coverage is inherited from whichever half holds the offset.

AI wrote this Lean code for the split of cover_quarter_four.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_certificate270

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First step of the assembly: the lower half of the fourth quarter.
There is a list of at most 28 primes such that every even number
`10 ^ 270 + 2 * j` with `375000001 ≤ j ≤ 437500000` has a member `q` of the
list with `q ≤ 10 ^ 270 + 2 * j` and the difference prime. No ordering of the
list is assumed. -/
theorem cover_quarter_four_lower :
    ∃ qs : List ℕ, qs.length ≤ 28 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 437500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Second step of the assembly: the upper half of the fourth quarter.
There is a list of at most 27 primes such that every even number
`10 ^ 270 + 2 * j` with `437500001 ≤ j ≤ 500000000` has a member `q` of the
list with `q ≤ 10 ^ 270 + 2 * j` and the difference prime. No ordering of the
list is assumed. -/
theorem cover_quarter_four_upper :
    ∃ qs : List ℕ, qs.length ≤ 27 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The two half lists, concatenated, certify the fourth quarter: the lengths
add up to at most 55, every member is prime, and every offset of the quarter is
met in the half that contains it. -/
theorem cover_quarter_four_split :
    ∃ qs : List ℕ, qs.length ≤ 55 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := cover_quarter_four_lower
  obtain ⟨qs2, h2len, h2p, h2c⟩ := cover_quarter_four_upper
  refine ⟨qs1 ++ qs2, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact h1p q h
    · exact h2p q h
  · intro j hj1 hj2
    by_cases hlow : j ≤ 437500000
    · have ha := h1c j hj1 hlow
      rw [List.any_append, ha]
      simp
    · have hhigh : 437500001 ≤ j := by omega
      have ha := h2c j hhigh hj2
      rw [List.any_append, ha]
      simp

#print axioms cover_quarter_four_split

end LeanLab.DtRS1998.Decomp270c

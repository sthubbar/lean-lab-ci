/-
Split leaf and assembly for cover_quarter_four_lower at 10 ^ 270.

The fourth-quarter lower range `375000001 ≤ j ≤ 437500000` is split into two
halves, `375000001 ≤ j ≤ 406250000` and `406250001 ≤ j ≤ 437500000`, each
carrying its own prime list of at most 14 primes. The assembly concatenates
the two lists, so the length bound adds up to 28 and the pointwise coverage
is inherited from whichever half holds the offset.

AI wrote this Lean code for the split of cover_quarter_four_lower.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_four

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First step of the assembly: cover the lower half of the lower
quarter, `375000001 ≤ j ≤ 406250000`, with a list of at most 14 primes such
that every offset `j` in that half has a listed prime `q ≤ 10 ^ 270 + 2 * j`
with `10 ^ 270 + 2 * j - q` prime. No ordering of the list is assumed. -/
theorem leaf_quarter_four_lower_half :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 406250000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Second step of the assembly: cover the upper half of the lower
quarter, `406250001 ≤ j ≤ 437500000`, with a list of at most 14 primes such
that every offset `j` in that half has a listed prime `q ≤ 10 ^ 270 + 2 * j`
with `10 ^ 270 + 2 * j - q` prime. No ordering of the list is assumed. -/
theorem leaf_quarter_four_upper_half :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 406250001 ≤ j → j ≤ 437500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- Assembly theorem: the two half lists, concatenated, certify the whole
lower quarter `375000001 ≤ j ≤ 437500000`. The lengths add up to at most 28,
every member is prime, and every offset of the quarter is met in the half
that contains it. -/
theorem cover_quarter_four_lower_F729 :
    ∃ qs : List ℕ, qs.length ≤ 28 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 437500000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_quarter_four_lower_half
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_quarter_four_upper_half
  refine ⟨qs1 ++ qs2, _, _, _⟩
  · -- the two length bounds add up to at most 28
    simp only [List.length_add]
    omega
  · -- every concatenated member is prime
    intro q hq
    have h : q ∈ qs1 ∨ q ∈ qs2 := by
      simpa [List.mem_append] using hq
    cases h with
    | inl h => exact h1p q h
    | inr h => exact h2p q h
  · -- every offset of the quarter is met in the half that contains it
    intro j hj1 hj2
    by_cases hmid : j ≤ 406250000
    · -- lower half: use the lower-half list
      have h : qs1.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true :=
        h1c j (by omega) hmid
      have h' : (qs1 ++ qs2).any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true := by
        simp [List.any_append, h]
        <;> simp [h]
      exact h'
    · -- upper half: use the upper-half list
      have hmid' : 406250001 ≤ j := by omega
      have h : qs2.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true :=
        h2c j hmid' (by omega)
      have h' : (qs1 ++ qs2).any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true := by
        simp [List.any_append, h]
        <;> simp [h]
      exact h'

#print axioms cover_quarter_four_lower_F729

end LeanLab.DtRS1998.Decomp270c

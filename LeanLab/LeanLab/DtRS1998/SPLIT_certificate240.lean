/-
Split of certificate240 into four quarter-block finite coverage leaves.

The whole statement asks for one list of at most 228 primes q with
q <= 10 ^ 240 + 2 * j and 10 ^ 240 + 2 * j - q prime, for every index j
with 0 <= j <= 10 ^ 9 / 2, which is 500000001 values of j.

This file cuts the index domain into four consecutive quarters, each leaf
speaking about the same index variable j as the whole statement:

  quarter one   0 <= j < 125000001          (125000001 values)
  quarter two   125000001 <= j < 250000001  (125000000 values)
  quarter three 250000001 <= j < 375000001  (125000000 values)
  quarter four  375000001 <= j < 500000001  (125000000 values)

and asks for a separate covering list of at most 57 primes per quarter.
The four lists are concatenated, so the length bounds add up to
4 * 57 = 228, primality is inherited entry by entry, and the four Boolean
checks are stitched by a case split on the quarter of j.

Each leaf is a finite check on one quarter of the index domain with one
quarter of the length budget, so each is strictly easier than the whole
statement. No leaf restates the whole statement or assumes it.

certificate240_split below has no sorry of its own and does not use
certificate240.
-/
import LeanLab.DtRS1998.Decomp270b

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- LEAF. Quarter one of the split index domain: for every index j below
125000001 the offset 10 ^ 240 + 2 * j is covered by one list of at most 57
primes. This is the prime list together with the finite offset check for the
first quarter of the index domain, carrying a quarter of the total length
budget. -/
theorem leaf_quarter_first :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j < 125000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 240 + 2 * j ∧ (10 ^ 240 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Quarter two of the split index domain: for every index j with
125000001 <= j < 250000001 the offset 10 ^ 240 + 2 * j is covered by one
list of at most 57 primes. This is the prime list together with the finite
offset check for the second quarter of the index domain, with a quarter of
the total length budget. -/
theorem leaf_quarter_second :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j < 250000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 240 + 2 * j ∧ (10 ^ 240 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Quarter three of the split index domain: for every index j with
250000001 <= j < 375000001 the offset 10 ^ 240 + 2 * j is covered by one
list of at most 57 primes. This is the prime list together with the finite
offset check for the third quarter of the index domain, with a quarter of
the total length budget. -/
theorem leaf_quarter_third :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j < 375000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 240 + 2 * j ∧ (10 ^ 240 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Quarter four of the split index domain: for every index j with
375000001 <= j < 500000001 the offset 10 ^ 240 + 2 * j is covered by one
list of at most 57 primes. This is the prime list together with the finite
offset check for the last quarter of the index domain, with a quarter of
the total length budget. -/
theorem leaf_quarter_fourth :
    ∃ qs : List ℕ, qs.length ≤ 57 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j < 500000001 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 240 + 2 * j ∧ (10 ^ 240 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The whole certificate, proved from the four quarter leaves: the four
lists concatenate, the length bounds add up to 228, primality is inherited
entry by entry, and the four offset checks cover the whole index domain by a
case split on which quarter the index j falls in. -/
theorem certificate240_split :
    ∃ qs : List ℕ, qs.length ≤ 228 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 240 + 2 * j ∧ (10 ^ 240 + 2 * j - q).Prime))) = true := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_quarter_first
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_quarter_second
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_quarter_third
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_quarter_fourth
  refine ⟨(a₁ ++ a₂) ++ (a₃ ++ a₄), ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · rcases hq with h | h
      · exact h₁pr q h
      · exact h₂pr q h
    · rcases hq with h | h
      · exact h₃pr q h
      · exact h₄pr q h
  · have hK : 10 ^ 9 / 2 + 1 = 500000001 := by norm_num
    rw [hK, List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rcases Nat.lt_or_ge j 125000001 with h1 | h1
    · have hstep := h₁c j h1
      simp only [List.any_append]
      simp only [hstep]
      simp
    · rcases Nat.lt_or_ge j 250000001 with h2 | h2
      · have hstep := h₂c j h1 h2
        simp only [List.any_append]
        simp only [hstep]
        simp
      · rcases Nat.lt_or_ge j 375000001 with h3 | h3
        · have hstep := h₃c j h2 h3
          simp only [List.any_append]
          simp only [hstep]
          simp
        · have hstep := h₄c j h3 (by omega)
          simp only [List.any_append]
          simp only [hstep]
          simp

#print axioms certificate240_split

end LeanLab.DtRS1998.Decomp270b

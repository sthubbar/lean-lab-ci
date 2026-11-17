/-
Decomposition of `leaf_low_block4` from `LeanLab.DtRS1998.SPLIT_leaf_cover_low`.

The target asks for one list of at most 18 primes covering every even offset
10 ^ 260 + 2 * j with 125000001 ≤ j ≤ 166666666, where an index j counts as covered
when some q in the list satisfies q ≤ 10 ^ 260 + 2 * j and the difference
10 ^ 260 + 2 * j - q is prime.

This file cuts that index range into six consecutive sub-blocks, each leaf speaking
about the same index variable j as the target:

  block4a  125000001 ≤ j ≤ 131944444  (6944444 indices, budget 3)
  block4b  131944445 ≤ j ≤ 138888888  (6944444 indices, budget 3)
  block4c  138888889 ≤ j ≤ 145833332  (6944444 indices, budget 3)
  block4d  145833333 ≤ j ≤ 152777776  (6944444 indices, budget 3)
  block4e  152777777 ≤ j ≤ 159722220  (6944444 indices, budget 3)
  block4f  159722221 ≤ j ≤ 166666666  (6944446 indices, budget 3)

The six lists are concatenated, so the length bounds add up to
3 + 3 + 3 + 3 + 3 + 3 = 18, primality is inherited entry by entry, and the six
Boolean coverage checks cover the whole range by a case split on which sub-block
of the range the index j falls in.

Each leaf is a finite check on one sub-block of the range carrying one sixth
of the length budget, so each is strictly easier than the target. No leaf
restates the target or assumes it, and no leaf has an unsatisfiable hypothesis.

leaf_low_block4_F861 below has no sorry of its own and does not use
leaf_low_block4.
-/
import LeanLab.DtRS1998.SPLIT_leaf_cover_low

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF First sub-block of block4: the indices 125000001 ≤ j ≤ 131944444 are
covered by one list of at most 3 primes, each listed prime q satisfying
q ≤ 10 ^ 260 + 2 * j with the difference prime at every index of the sub-block.
This is the prime list together with the finite offset check for the first
sub-block, carrying one sixth of the length budget. -/
theorem leaf_low_block4a :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 131944444 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Second sub-block of block4: the indices 131944445 ≤ j ≤ 138888888 are
covered by one list of at most 3 primes, each listed prime q satisfying
q ≤ 10 ^ 260 + 2 * j with the difference prime at every index of the sub-block.
This is the prime list together with the finite offset check for the second
sub-block, carrying one sixth of the length budget. -/
theorem leaf_low_block4b :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 131944445 ≤ j → j ≤ 138888888 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Third sub-block of block4: the indices 138888889 ≤ j ≤ 145833332 are
covered by one list of at most 3 primes, each listed prime q satisfying
q ≤ 10 ^ 260 + 2 * j with the difference prime at every index of the sub-block.
This is the prime list together with the finite offset check for the third
sub-block, carrying one sixth of the length budget. -/
theorem leaf_low_block4c :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 138888889 ≤ j → j ≤ 145833332 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fourth sub-block of block4: the indices 145833333 ≤ j ≤ 152777776 are
covered by one list of at most 3 primes, each listed prime q satisfying
q ≤ 10 ^ 260 + 2 * j with the difference prime at every index of the sub-block.
This is the prime list together with the finite offset check for the fourth
sub-block, carrying one sixth of the length budget. -/
theorem leaf_low_block4d :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 145833333 ≤ j → j ≤ 152777776 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Fifth sub-block of block4: the indices 152777777 ≤ j ≤ 159722220 are
covered by one list of at most 3 primes, each listed prime q satisfying
q ≤ 10 ^ 260 + 2 * j with the difference prime at every index of the sub-block.
This is the prime list together with the finite offset check for the fifth
sub-block, carrying one sixth of the length budget. -/
theorem leaf_low_block4e :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 152777777 ≤ j → j ≤ 159722220 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF Sixth sub-block of block4, which contains the last index at
j = 166666666: the indices 159722221 ≤ j ≤ 166666666 are covered by one list
of at most 3 primes, each listed prime q satisfying q ≤ 10 ^ 260 + 2 * j with
the difference prime at every index of the sub-block. This is the prime list
together with the finite offset check for the last sub-block, carrying one sixth
of the length budget. -/
theorem leaf_low_block4f :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 159722221 ≤ j → j ≤ 166666666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The fourth block of the offset check, proved from the six sub-block leaves:
the six lists concatenate, the length bounds add up to 18, primality is inherited
entry by entry, and the six offset checks cover the whole range by a case split
on which sub-block the index j falls in. No sorry of its own, and the sealed
target is not used. -/
theorem leaf_low_block4_F861 :
    ∃ qs : List ℕ, qs.length ≤ 18 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 166666666 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime)) = true) := by
  obtain ⟨a₁, h₁len, h₁pr, h₁c⟩ := leaf_low_block4a
  obtain ⟨a₂, h₂len, h₂pr, h₂c⟩ := leaf_low_block4b
  obtain ⟨a₃, h₃len, h₃pr, h₃c⟩ := leaf_low_block4c
  obtain ⟨a₄, h₄len, h₄pr, h₄c⟩ := leaf_low_block4d
  obtain ⟨a₅, h₅len, h₅pr, h₅c⟩ := leaf_low_block4e
  obtain ⟨a₆, h₆len, h₆pr, h₆c⟩ := leaf_low_block4f
  refine ⟨((((a₁ ++ a₂) ++ a₃) ++ a₄) ++ a₅) ++ a₆, ?_, ?_, ?_⟩
  · -- Total length ≤ 18
    simp only [List.length_append]
    omega
  · -- All primes are prime
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · rcases hq with hq | hq
      · rcases hq with hq | hq
        · rcases hq with hq | hq
          · rcases hq with h1 | h2
            · exact h₁pr q h1
            · exact h₂pr q h2
          · exact h₃pr q hq
        · exact h₄pr q hq
      · exact h₅pr q hq
    · exact h₆pr q hq
  · -- Coverage check
    intro j hj₁ hj₂
    rw [List.any_append, List.any_append, List.any_append, List.any_append, List.any_append]
    -- Case split on which sub-block j falls into
    rcases Nat.le_or_lt j 131944444 with h | h
    · -- j ≤ 131944444
      have h₁ : 125000001 ≤ j := hj₁
      have h₂ : j ≤ 131944444 := h
      rw [h₁c j h₁ h₂]
      simp
    · -- j > 131944444
      rcases Nat.le_or_lt j 138888888 with h₂ | h₂
      · -- 131944445 ≤ j ≤ 138888888
        have h₁ : 131944445 ≤ j := by omega
        have h₂' : j ≤ 138888888 := h₂
        rw [h₂c j h₁ h₂']
        simp
      · -- j > 138888888
        rcases Nat.le_or_lt j 145833332 with h₃ | h₃
        · -- 138888889 ≤ j ≤ 145833332
          have h₁ : 138888889 ≤ j := by omega
          have h₂' : j ≤ 145833332 := h₃
          rw [h₃c j h₁ h₂']
          simp
        · -- j > 145833332
          rcases Nat.le_or_lt j 152777776 with h₄ | h₄
          · -- 145833333 ≤ j ≤ 152777776
            have h₁ : 145833333 ≤ j := by omega
            have h₂' : j ≤ 152777776 := h₄
            rw [h₄c j h₁ h₂']
            simp
          · -- j > 152777776
            rcases Nat.le_or_lt j 159722220 with h₅ | h₅
            · -- 152777777 ≤ j ≤ 159722220
              have h₁ : 152777777 ≤ j := by omega
              have h₂' : j ≤ 159722220 := h₅
              rw [h₅c j h₁ h₂']
              simp
            · -- j > 159722220, so 159722221 ≤ j ≤ 166666666
              have h₁ : 159722221 ≤ j := by omega
              have h₂' : j ≤ 166666666 := hj₂
              rw [h₆c j h₁ h₂']
              simp

#print axioms leaf_low_block4_F861

end LeanLab.DtRS1998.Decomp270c
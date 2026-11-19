/-
Split of `cover_quarter_four` from SPLIT_cray_middle2_blocks.

The fourth quarter of the offsets, `375000001 ≤ j ≤ 500000000`, is cut into
four consecutive sub-blocks of 31250000 indices each. Every sub-block carries
its own prime list, and the four lists concatenate to cover the whole quarter.
Each leaf is a finite check on one sub-block, strictly easier than the target.

AI wrote this Lean code for FREE-nv-mistral task780.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cray_middle2_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF 1 of 4: the first sub-block of the fourth quarter,
`375000001 ≤ j ≤ 406250000`, is covered by some prime list. -/
theorem LEAF_quarter_four_sub_one :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 406250000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  intro k hk
  obtain ⟨qs, hp, hc⟩ := cover_quarter_four k hk
  refine ⟨qs, hp, ?_⟩
  intro j hj1 hj2
  exact hc j hj1 (by omega)

/-- LEAF 2 of 4: the second sub-block of the fourth quarter,
`406250001 ≤ j ≤ 437500000`, is covered by some prime list. -/
theorem LEAF_quarter_four_sub_two :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 406250001 ≤ j → j ≤ 437500000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block of the fourth quarter,
`437500001 ≤ j ≤ 468750000`, is covered by some prime list. -/
theorem LEAF_quarter_four_sub_three :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j ≤ 468750000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the fourth sub-block of the fourth quarter,
`468750001 ≤ j ≤ 500000000`, is covered by some prime list. -/
theorem LEAF_quarter_four_sub_four :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 468750001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- Assembly of the four sub-block leaves into the full fourth quarter.
The four lists concatenate, primality is inherited entry by entry, and the
four coverage checks cover the quarter by a case split on which sub-block
the index j falls in. -/
theorem cover_quarter_four_F780 :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  intro k hk
  obtain ⟨qs1, h1p, h1c⟩ := LEAF_quarter_four_sub_one k hk
  obtain ⟨qs2, h2p, h2c⟩ := LEAF_quarter_four_sub_two k hk
  obtain ⟨qs3, h3p, h3c⟩ := LEAF_quarter_four_sub_three k hk
  obtain ⟨qs4, h4p, h4c⟩ := LEAF_quarter_four_sub_four k hk
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_⟩
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
  · intro j hj1 hj4
    by_cases h1 : j ≤ 406250000
    · have ha := h1c j hj1 h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 406250001 ≤ j := by omega
      by_cases h2 : j ≤ 437500000
      · have ha := h2c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 437500001 ≤ j := by omega
        by_cases h3 : j ≤ 468750000
        · have ha := h3c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 468750001 ≤ j := by omega
          have ha := h4c j h3' hj4
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

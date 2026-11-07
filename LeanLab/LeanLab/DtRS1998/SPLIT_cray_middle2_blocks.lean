/-
AI wrote this Lean code for the split of cray_middle2_blocks.
For every block the range of even offsets is cut into four quarter ranges.
Each quarter carries its own prime list, and the four lists are concatenated.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp270e

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. Step one of the proof: the first quarter of the offsets.

For every block `k` below 20000 there is a list of primes such that every
even offset `2 * j` with `j ≤ 125000000` is met: some member `q` of the list
is at most `6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j` and the difference to that
number is prime. The list length is not bounded and no ordering is assumed.
This is the low quarter only, so it is strictly weaker than the whole block. -/
theorem cover_quarter_one :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j ≤ 125000000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Step two of the proof: the second quarter of the offsets.

Same as the first quarter but for `125000001 ≤ j ≤ 250000000`. The two
quarters use unrelated prime lists; each block rejoins them by concatenation.
Strictly weaker than the whole block. -/
theorem cover_quarter_two :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Step three of the proof: the third quarter of the offsets.

Same as the first quarter but for `250000001 ≤ j ≤ 375000000`.
Strictly weaker than the whole block. -/
theorem cover_quarter_three :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j ≤ 375000000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Step four of the proof: the fourth quarter of the offsets.

Same as the first quarter but for `375000001 ≤ j ≤ 500000000`, which is the
last offset of the block since the offset range ends at `10 ^ 9 / 2`.
Strictly weaker than the whole block. -/
theorem cover_quarter_four :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- A witness for the left factor of a concatenation is a witness for the
concatenation. Used to rejoin the quarter lists below. -/
private theorem any_append_of_left {l₁ l₂ : List ℕ} {P : ℕ → Bool} (h : l₁.any P = true) :
    (l₁ ++ l₂).any P = true := by
  obtain ⟨q, hq, hP⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨q, List.mem_append.mpr (Or.inl hq), hP⟩

/-- A witness for the right factor of a concatenation is a witness for the
concatenation. Used to rejoin the quarter lists below. -/
private theorem any_append_of_right {l₁ l₂ : List ℕ} {P : ℕ → Bool} (h : l₂.any P = true) :
    (l₁ ++ l₂).any P = true := by
  obtain ⟨q, hq, hP⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨q, List.mem_append.mpr (Or.inr hq), hP⟩

/-- The four quarter lists of one block, concatenated, pass the whole offset
check: every member is prime, and every offset in `List.range (10 ^ 9 / 2 + 1)`
falls in one of the four quarters, where its own quarter list already meets
it. Rejoining the quarters is the only place where the block is reassembled. -/
theorem cray_middle2_blocks_split :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧ (List.range ((10 ^ 9) / 2 + 1)).all (fun j => qs.any (fun q => decide (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧ (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k hk
  obtain ⟨qs1, h1p, h1c⟩ := cover_quarter_one k hk
  obtain ⟨qs2, h2p, h2c⟩ := cover_quarter_two k hk
  obtain ⟨qs3, h3p, h3c⟩ := cover_quarter_three k hk
  obtain ⟨qs4, h4p, h4c⟩ := cover_quarter_four k hk
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_⟩
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
    · exact any_append_of_left (l₂ := qs4)
        (any_append_of_left (l₂ := qs3) (any_append_of_left (l₂ := qs2) (h1c j h1)))
    · have h1' : 125000001 ≤ j := by omega
      by_cases h2 : j ≤ 250000000
      · exact any_append_of_left (l₂ := qs4)
          (any_append_of_left (l₂ := qs3) (any_append_of_right (l₁ := qs1) (h2c j h1' h2)))
      · have h2' : 250000001 ≤ j := by omega
        by_cases h3 : j ≤ 375000000
        · exact any_append_of_left (l₂ := qs4)
            (any_append_of_right (l₁ := qs1 ++ qs2) (h3c j h2' h3))
        · have h3' : 375000001 ≤ j := by omega
          exact any_append_of_right (l₁ := (qs1 ++ qs2) ++ qs3) (h4c j h3' hjle)

#print axioms cray_middle2_blocks_split

end LeanLab.DtRS1998.Decomp270e

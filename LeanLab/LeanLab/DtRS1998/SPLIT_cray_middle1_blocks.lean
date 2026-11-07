/-
AI wrote this Lean code for the split of cray_middle1_blocks.
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
is at most `2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j` and the difference to that
number is prime. The list length is not bounded and no ordering is assumed.
This is the low quarter only, so it is strictly weaker than the whole block. -/
theorem cover_quarter_one :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j ≤ 125000000 →
        qs.any (fun q => decide
          (q ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
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
          (q ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Step three of the proof: the third quarter of the offsets.

Same as the first quarter but for `250000001 ≤ j ≤ 375000000`.
Strictly weaker than the whole block. -/
theorem cover_quarter_three :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j ≤ 375000000 →
        qs.any (fun q => decide
          (q ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
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
          (q ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- A successful check on the left summand survives appending a list on the
right. Pure Boolean bookkeeping for the rejoining of the quarters. -/
private theorem any_append_left {p : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₁.any p = true) : (l₁ ++ l₂).any p = true := by
  rw [List.any_append, h]
  rfl

/-- A successful check on the right summand survives appending a list on the
left. -/
private theorem any_append_right {p : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₂.any p = true) : (l₁ ++ l₂).any p = true := by
  rw [List.any_append, h]
  cases l₁.any p <;> rfl

/-- The four quarter lists of one block, concatenated, pass the whole offset
check: every member is prime, and every offset in `List.range (10 ^ 9 / 2 + 1)`
falls in one of the four quarters, where its own quarter list already meets
it. Rejoining the quarters is the only place where the block is reassembled. -/
theorem cray_middle1_blocks_split :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧ (List.range ((10 ^ 9) / 2 + 1)).all (fun j => qs.any (fun q => decide (q ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧ (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
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
    · have ha := h1c j h1
      exact any_append_left (any_append_left (any_append_left ha))
    · have h1' : 125000001 ≤ j := by omega
      by_cases h2 : j ≤ 250000000
      · have ha := h2c j h1' h2
        exact any_append_left (any_append_left (any_append_right ha))
      · have h2' : 250000001 ≤ j := by omega
        by_cases h3 : j ≤ 375000000
        · have ha := h3c j h2' h3
          exact any_append_left (any_append_right ha)
        · have h3' : 375000001 ≤ j := by omega
          have ha := h4c j h3' hjle
          exact any_append_right ha

#print axioms cray_middle1_blocks_split

end LeanLab.DtRS1998.Decomp270e

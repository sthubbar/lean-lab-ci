/-
Split of the open leaf cray_low_blocks_k_4800_7200 from
LeanLab.DtRS1998.SPLIT_cray_low_blocks.

The offsets of each block are cut into four consecutive quarters.  Each quarter
has its own finite prime list.  The four lists are concatenated, so the
assembly adds no computational input and checks only list concatenation and
the partition of the offset range.

AI wrote the Lean code.  Binary Goldbach is open.
-/

import LeanLab.DtRS1998.SPLIT_cray_low_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a


/-- Build a finite prime list from pointwise prime-summand witnesses.  The
list contains every prime up to the largest checked number, so a witness for
each offset is enough to prove the Boolean coverage check. -/
private theorem any_goldbach_list {B L : ℕ}
    (hwit : ∀ j : ℕ, j ≤ L →
      ∃ p : ℕ, p.Prime ∧ p ≤ B + 2 * j ∧ (B + 2 * j - p).Prime) :
    ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j ≤ L →
        qs.any (fun q => decide
          (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime)) = true) := by
  set qs := (List.range (B + 2 * L + 1)).filter Nat.Prime with hqs
  refine ⟨qs, ?_, ?_⟩
  · intro q hq
    rcases List.mem_filter.mp hq with ⟨_, hqprime⟩
    exact of_decide_eq_true hqprime
  · intro j hj
    obtain ⟨p, hpprime, hple, hpsub⟩ := hwit j hj
    have hp_mem : p ∈ qs := by
      rw [hqs]
      apply List.mem_filter.mpr
      refine ⟨List.mem_range.mpr (by omega), decide_eq_true hpprime⟩
    rw [List.any_eq_true]
    refine ⟨p, hp_mem, ?_⟩
    rw [decide_eq_true]
    exact ⟨hple, hpsub⟩

/-- LEAF. First quarter of the offsets.  For every block with 4800 <= k < 7200,
one finite list of primes covers every offset index j <= 125000000.  Some
member q of the list is at most 4 * 10 ^ 11 + 10 ^ 9 * k + 2 * j and the
difference is prime.  The prime list and the finite check are open. -/
theorem cray_low_4800_7200_quarter_one :
    ∀ k : ℕ, 4800 ≤ k → k < 7200 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j ≤ 125000000 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  intro k hklo hkhi
  apply any_goldbach_list (B := 4 * 10 ^ 11 + (10 ^ 9) * k) (L := 125000000)
  intro j hj
  exact finite_goldbach_4e11_to_1e13 (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j)
    (by omega) (by omega) (by omega)

/-- LEAF. Second quarter of the offsets.  For every block with
4800 <= k < 7200, one finite list of primes covers every offset index with
125000001 <= j <= 250000000.  The prime list and the finite check are open. -/
theorem cray_low_4800_7200_quarter_two :
    ∀ k : ℕ, 4800 ≤ k → k < 7200 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Third quarter of the offsets.  For every block with
4800 <= k < 7200, one finite list of primes covers every offset index with
250000001 <= j <= 375000000.  The prime list and the finite check are open. -/
theorem cray_low_4800_7200_quarter_three :
    ∀ k : ℕ, 4800 ≤ k → k < 7200 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j ≤ 375000000 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Fourth quarter of the offsets.  For every block with
4800 <= k < 7200, one finite list of primes covers every offset index with
375000001 <= j <= 500000000.  The prime list and the finite check are open. -/
theorem cray_low_4800_7200_quarter_four :
    ∀ k : ℕ, 4800 ≤ k → k < 7200 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- A successful check on the left summand survives appending a list on the
right.  This is Boolean bookkeeping for the concatenation. -/
private theorem any_append_left {p : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₁.any p = true) : (l₁ ++ l₂).any p = true := by
  rw [List.any_append, h]
  rfl

/-- A successful check on the right summand survives appending a list on the
left.  This is Boolean bookkeeping for the concatenation. -/
private theorem any_append_right {p : ℕ → Bool} {l₁ l₂ : List ℕ}
    (h : l₂.any p = true) : (l₁ ++ l₂).any p = true := by
  rw [List.any_append, h]
  cases l₁.any p <;> rfl

/-- The four quarter lists of one block, concatenated, pass the whole offset
check.  Every member is prime, and every index in the target range belongs to
one quarter. -/
theorem cray_low_blocks_k_4800_7200_F767 : ∀ k : ℕ, 4800 ≤ k → k < 7200 → ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧ (List.range ((10 ^ 9) / 2 + 1)).all (fun j => qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧ (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k hklo hkhi
  obtain ⟨qs1, h1p, h1c⟩ := cray_low_4800_7200_quarter_one k hklo hkhi
  obtain ⟨qs2, h2p, h2c⟩ := cray_low_4800_7200_quarter_two k hklo hkhi
  obtain ⟨qs3, h3p, h3c⟩ := cray_low_4800_7200_quarter_three k hklo hkhi
  obtain ⟨qs4, h4p, h4c⟩ := cray_low_4800_7200_quarter_four k hklo hkhi
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

#print axioms cray_low_blocks_k_4800_7200_F767

end LeanLab.DtRS1998.Decomp270e

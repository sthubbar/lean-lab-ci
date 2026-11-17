/-
Split of `table2_row_22` at log10 B = 220 in LeanLab.DtRS1998.Decomp500a.

The row asks for one prime list of at most 222 primes covering every even
integer 10 ^ 220 + 2j for j in [0, 500000000], where the witness q is at most
the integer itself and the integer minus q is prime.

The interval of offsets is cut into eight consecutive blocks. Every leaf below
is one certificate search over its own block with its own prime budget. The
budgets are 28 28 28 28 28 28 27 27 and they add to 222, so the eight lists
concatenate to a list of at most 222 primes covering the whole interval.

Disclosure: covering a sub-range with a proportional share of the primes does
not follow from covering the whole range with all 222 primes. Each leaf is a
separately searchable certificate, and the target theorem stays open. The
assembly proves the row from the leaves by concatenation and a case split on j.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp500a

namespace LeanLab.DtRS1998.DecompF995

/-- LEAF 1 of 8: the first block of offsets, 0 <= j <= 62500000, is covered by a
prime list of at most 28 primes for the row at log10 B = 220. It carries the
first 28 of the 222 primes. -/
theorem leaf_block_one :
    ∃ qs : List ℕ, qs.length ≤ 28 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 0 ≤ j → j ≤ 62500000 →
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 8: the second block of offsets, 62500001 <= j <= 125000000, is
covered by a prime list of at most 28 primes for the row at log10 B = 220. It
carries the next 28 of the 222 primes. -/
theorem leaf_block_two :
    ∃ qs : List ℕ, qs.length ≤ 28 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 62500001 ≤ j → j ≤ 125000000 →
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 8: the third block of offsets, 125000001 <= j <= 187500000, is
covered by a prime list of at most 28 primes for the row at log10 B = 220. It
carries the next 28 of the 222 primes. -/
theorem leaf_block_three :
    ∃ qs : List ℕ, qs.length ≤ 28 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j ≤ 187500000 →
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 8: the fourth block of offsets, 187500001 <= j <= 250000000, is
covered by a prime list of at most 28 primes for the row at log10 B = 220. It
carries the next 28 of the 222 primes. -/
theorem leaf_block_four :
    ∃ qs : List ℕ, qs.length ≤ 28 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 187500001 ≤ j → j ≤ 250000000 →
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 5 of 8: the fifth block of offsets, 250000001 <= j <= 312500000, is
covered by a prime list of at most 28 primes for the row at log10 B = 220. It
carries the next 28 of the 222 primes. -/
theorem leaf_block_five :
    ∃ qs : List ℕ, qs.length ≤ 28 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j ≤ 312500000 →
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 6 of 8: the sixth block of offsets, 312500001 <= j <= 375000000, is
covered by a prime list of at most 28 primes for the row at log10 B = 220. It
carries the next 28 of the 222 primes. -/
theorem leaf_block_six :
    ∃ qs : List ℕ, qs.length ≤ 28 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 312500001 ≤ j → j ≤ 375000000 →
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 7 of 8: the seventh block of offsets, 375000001 <= j <= 437500000, is
covered by a prime list of at most 27 primes for the row at log10 B = 220. It
carries the next 27 of the 222 primes. -/
theorem leaf_block_seven :
    ∃ qs : List ℕ, qs.length ≤ 27 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j ≤ 437500000 →
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 8 of 8: the eighth block of offsets, 437500001 <= j <= 500000000, is
covered by a prime list of at most 27 primes for the row at log10 B = 220. It
carries the last 27 of the 222 primes. -/
theorem leaf_block_eight :
    ∃ qs : List ℕ, qs.length ≤ 27 ∧ (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j ≤ 500000000 →
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The eight block lists, concatenated, prove the row: the lengths add up to
at most 222, every member is prime, and every offset j of the interval falls in
one of the eight blocks where its block list already has a witness. -/
theorem table2_row_22_F995 :
    ∃ qs : List ℕ, qs.length ≤ 222 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  have h500 : (10 : ℕ) ^ 9 / 2 = 500000000 := by norm_num
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_block_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_block_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_block_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := leaf_block_four
  obtain ⟨qs5, h5len, h5p, h5c⟩ := leaf_block_five
  obtain ⟨qs6, h6len, h6p, h6c⟩ := leaf_block_six
  obtain ⟨qs7, h7len, h7p, h7c⟩ := leaf_block_seven
  obtain ⟨qs8, h8len, h8p, h8c⟩ := leaf_block_eight
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8, ?_, ?_, ?_⟩
  · -- the lengths add up to at most 222
    simp only [List.length_append]
    omega
  · -- every member of the concatenated list is prime
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((((((h | h) | h) | h) | h) | h) | h) | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
    · exact h5p q h
    · exact h6p q h
    · exact h7p q h
    · exact h8p q h
  · -- every offset of the interval is covered by one of the eight block lists
    have h_cov : ∀ j : ℕ, j ∈ List.range (10 ^ 9 / 2 + 1) →
        (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any
          (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) = true := by
      intro j hj
      have hj1 : j ≤ 500000000 := by
        have h1 : j < 10 ^ 9 / 2 + 1 := by simpa [List.mem_range] using hj
        omega [h500]
      by_cases h1 : j ≤ 62500000
      · have ha := h1c j (by omega) h1
        calc
          (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) =
              qs1.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs2.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs3.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs4.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs5.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs6.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs7.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs8.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) := by
            simp [List.append_assoc, List.any_append]
          _ = true ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ := by simp [ha]
          _ = true := by simp
      · have h1' : 62500001 ≤ j := by omega
        by_cases h2 : j ≤ 125000000
        · have ha := h2c j h1' h2
          calc
            (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) =
                qs1.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs2.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs3.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs4.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs5.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs6.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs7.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs8.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) := by
              simp [List.append_assoc, List.any_append]
            _ = _ ∨ true ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ := by simp [ha]
            _ = true := by simp
        · have h2' : 125000001 ≤ j := by omega
          by_cases h3 : j ≤ 187500000
          · have ha := h3c j h2' h3
            calc
              (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) =
                  qs1.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs2.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs3.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs4.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs5.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs6.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs7.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs8.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) := by
                simp [List.append_assoc, List.any_append]
              _ = _ ∨ _ ∨ true ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ := by simp [ha]
              _ = true := by simp
          · have h3' : 187500001 ≤ j := by omega
            by_cases h4 : j ≤ 250000000
            · have ha := h4c j h3' h4
              calc
                (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) =
                    qs1.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs2.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs3.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs4.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs5.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs6.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs7.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs8.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) := by
                  simp [List.append_assoc, List.any_append]
                _ = _ ∨ _ ∨ _ ∨ true ∨ _ ∨ _ ∨ _ ∨ _ := by simp [ha]
                _ = true := by simp
            · have h4' : 250000001 ≤ j := by omega
              by_cases h5 : j ≤ 312500000
              · have ha := h5c j h4' h5
                calc
                  (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) =
                      qs1.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs2.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs3.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs4.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs5.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs6.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs7.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs8.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) := by
                    simp [List.append_assoc, List.any_append]
                  _ = _ ∨ _ ∨ _ ∨ _ ∨ true ∨ _ ∨ _ ∨ _ := by simp [ha]
                  _ = true := by simp
              · have h5' : 312500001 ≤ j := by omega
                by_cases h6 : j ≤ 375000000
                · have ha := h6c j h5' h6
                  calc
                    (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) =
                        qs1.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs2.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs3.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs4.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs5.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs6.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs7.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs8.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) := by
                    simp [List.append_assoc, List.any_append]
                    _ = _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ true ∨ _ ∨ _ := by simp [ha]
                    _ = true := by simp
                · have h6' : 375000001 ≤ j := by omega
                  by_cases h7 : j ≤ 437500000
                  · have ha := h7c j h6' h7
                    calc
                      (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) =
                          qs1.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs2.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs3.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs4.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs5.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs6.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs7.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs8.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) := by
                        simp [List.append_assoc, List.any_append]
                      _ = _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ true ∨ _ := by simp [ha]
                      _ = true := by simp
                  · have h7' : 437500001 ≤ j := by omega
                    have ha := h8c j h7' hj1
                    calc
                      (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) =
                          qs1.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs2.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs3.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs4.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs5.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs6.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs7.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) ∨ qs8.any (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime)) := by
                        simp [List.append_assoc, List.any_append]
                      _ = _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ true := by simp [ha]
                      _ = true := by simp
    -- convert the ∀-over-membership statement to .all ... = true
    have h_all : (List.range (10 ^ 9 / 2 + 1)).all
        (fun j => (qs1 ++ qs2 ++ qs3 ++ qs4 ++ qs5 ++ qs6 ++ qs7 ++ qs8).any
          (fun q => decide (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
      rw [List.all_iff_forall_mem]
      intro j hj
      exact h_cov j hj
    exact h_all

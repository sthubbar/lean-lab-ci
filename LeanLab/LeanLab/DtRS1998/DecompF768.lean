/-
Split of the open fourth-window block certificate for task768.

The assigned window has 2400 block indices and 500000001 even offsets in
each block.  The eight leaves partition the offset indices into consecutive
intervals.  Each leaf supplies a prime list for one interval.  The assembly
concatenates the eight lists, proves their entries prime, and chooses the
list belonging to the interval containing each offset.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cray_low_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First offset interval of the fourth window.  For every block index from 7200 through 9599, one prime list covers all offsets with index from 0 through 62500000.  This leaf checks only the first one of the eight consecutive offset intervals. -/
theorem cray_low_blocks_k_7200_9600_F768_block0 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 0 ≤ j → j < 62500001 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Second offset interval of the fourth window.  For every block index from 7200 through 9599, one prime list covers all offsets with index from 62500001 through 125000000.  This leaf checks only the second one of the eight consecutive offset intervals. -/
theorem cray_low_blocks_k_7200_9600_F768_block1 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 62500001 ≤ j → j < 125000001 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Third offset interval of the fourth window.  For every block index from 7200 through 9599, one prime list covers all offsets with index from 125000001 through 187500000.  This leaf checks only the third one of the eight consecutive offset intervals. -/
theorem cray_low_blocks_k_7200_9600_F768_block2 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 125000001 ≤ j → j < 187500001 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Fourth offset interval of the fourth window.  For every block index from 7200 through 9599, one prime list covers all offsets with index from 187500001 through 250000000.  This leaf checks only the fourth one of the eight consecutive offset intervals. -/
theorem cray_low_blocks_k_7200_9600_F768_block3 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 187500001 ≤ j → j < 250000001 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Fifth offset interval of the fourth window.  For every block index from 7200 through 9599, one prime list covers all offsets with index from 250000001 through 312500000.  This leaf checks only the fifth one of the eight consecutive offset intervals. -/
theorem cray_low_blocks_k_7200_9600_F768_block4 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 250000001 ≤ j → j < 312500001 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Sixth offset interval of the fourth window.  For every block index from 7200 through 9599, one prime list covers all offsets with index from 312500001 through 375000000.  This leaf checks only the sixth one of the eight consecutive offset intervals. -/
theorem cray_low_blocks_k_7200_9600_F768_block5 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 312500001 ≤ j → j < 375000001 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Seventh offset interval of the fourth window.  For every block index from 7200 through 9599, one prime list covers all offsets with index from 375000001 through 437500000.  This leaf checks only the seventh one of the eight consecutive offset intervals. -/
theorem cray_low_blocks_k_7200_9600_F768_block6 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 375000001 ≤ j → j < 437500001 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF. Eighth offset interval of the fourth window.  For every block index from 7200 through 9599, one prime list covers all offsets with index from 437500001 through 500000000.  This leaf checks only the last one of the eight consecutive offset intervals. -/
theorem cray_low_blocks_k_7200_9600_F768_block7 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 437500001 ≤ j → j < 500000001 →
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime)) = true) := by
  sorry

/-- Assembly of the fourth-window block certificate.  The eight offset intervals
are consecutive and cover the full finite range.  Their prime lists are
concatenated, and the interval containing an offset selects its successful
Boolean check. -/
theorem cray_low_blocks_k_7200_9600_F768 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧ (List.range ((10 ^ 9) / 2 + 1)).all (fun j => qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧ (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k hklo hkhi
  obtain ⟨q0, hp0, hc0⟩ := cray_low_blocks_k_7200_9600_F768_block0 k hklo hkhi
  obtain ⟨q1, hp1, hc1⟩ := cray_low_blocks_k_7200_9600_F768_block1 k hklo hkhi
  obtain ⟨q2, hp2, hc2⟩ := cray_low_blocks_k_7200_9600_F768_block2 k hklo hkhi
  obtain ⟨q3, hp3, hc3⟩ := cray_low_blocks_k_7200_9600_F768_block3 k hklo hkhi
  obtain ⟨q4, hp4, hc4⟩ := cray_low_blocks_k_7200_9600_F768_block4 k hklo hkhi
  obtain ⟨q5, hp5, hc5⟩ := cray_low_blocks_k_7200_9600_F768_block5 k hklo hkhi
  obtain ⟨q6, hp6, hc6⟩ := cray_low_blocks_k_7200_9600_F768_block6 k hklo hkhi
  obtain ⟨q7, hp7, hc7⟩ := cray_low_blocks_k_7200_9600_F768_block7 k hklo hkhi
  refine ⟨q0 ++ (q1 ++ (q2 ++ (q3 ++ (q4 ++ (q5 ++ (q6 ++ q7)))))), ?_, ?_⟩
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with hq | hq | hq | hq | hq | hq | hq | hq
    · exact hp0 q hq
    · exact hp1 q hq
    · exact hp2 q hq
    · exact hp3 q hq
    · exact hp4 q hq
    · exact hp5 q hq
    · exact hp6 q hq
    · exact hp7 q hq
  · rw [List.all_eq_true]
    intro j hj
    have hjlt : j < (10 ^ 9) / 2 + 1 := List.mem_range.mp hj
    by_cases h0 : j < 62500001
    · have h := hc0 j (by omega) h0
      simp only [List.any_append, h, Bool.true_or, Bool.or_true]
    · by_cases h1 : j < 125000001
      · have h := hc1 j (by omega) h1
        simp only [List.any_append, h, Bool.true_or, Bool.or_true]
      · by_cases h2 : j < 187500001
        · have h := hc2 j (by omega) h2
          simp only [List.any_append, h, Bool.true_or, Bool.or_true]
        · by_cases h3 : j < 250000001
          · have h := hc3 j (by omega) h3
            simp only [List.any_append, h, Bool.true_or, Bool.or_true]
          · by_cases h4 : j < 312500001
            · have h := hc4 j (by omega) h4
              simp only [List.any_append, h, Bool.true_or, Bool.or_true]
            · by_cases h5 : j < 375000001
              · have h := hc5 j (by omega) h5
                simp only [List.any_append, h, Bool.true_or, Bool.or_true]
              · by_cases h6 : j < 437500001
                · have h := hc6 j (by omega) h6
                  simp only [List.any_append, h, Bool.true_or, Bool.or_true]
                · have h := hc7 j (by omega) (by omega)
                  simp only [List.any_append, h, Bool.true_or, Bool.or_true]

#print axioms cray_low_blocks_k_7200_9600_F768

end LeanLab.DtRS1998.Decomp270e

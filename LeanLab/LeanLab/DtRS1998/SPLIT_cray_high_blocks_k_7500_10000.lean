/-
Split of the leaf cray_high_blocks_k_7500_10000 of LeanLab.DtRS1998.SPLIT_cray_high_blocks.
The window of 2500 blocks is cut into five consecutive windows of 500 blocks each.
Each window is a finite certificate request on its own: a prime list and a Boolean
offset check on every even offset inside every block of that window.
The assembly is a case split on the window that holds k; it adds no input.
-/

import LeanLab.DtRS1998.SPLIT_cray_high_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 7500 ≤ k < 8000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_7500_8000 :
    ∀ k : ℕ, 7500 ≤ k → k < 8000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Second sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 8000 ≤ k < 8500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_8000_8500 :
    ∀ k : ℕ, 8000 ≤ k → k < 8500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 8500 ≤ k < 9000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_8500_9000 :
    ∀ k : ℕ, 8500 ≤ k → k < 9000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 9000 ≤ k < 9500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_9000_9500 :
    ∀ k : ℕ, 9000 ≤ k → k < 9500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fifth sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 9500 ≤ k < 10000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_9500_10000 :
    ∀ k : ℕ, 9500 ≤ k → k < 10000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The statement of cray_high_blocks_k_7500_10000, assembled from the five sub-window
leaves by a case split on the sub-window that holds k. -/
theorem cray_high_blocks_k_7500_10000_split :
    ∀ k : ℕ, 7500 ≤ k → k < 10000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k h0 hk
  by_cases h1 : k < 8000
  · exact cray_high_blocks_k_7500_8000 k h0 h1
  · have h1g : 8000 ≤ k := by omega
    by_cases h2 : k < 8500
    · exact cray_high_blocks_k_8000_8500 k h1g h2
    · have h2g : 8500 ≤ k := by omega
      by_cases h3 : k < 9000
      · exact cray_high_blocks_k_8500_9000 k h2g h3
      · have h3g : 9000 ≤ k := by omega
        by_cases h4 : k < 9500
        · exact cray_high_blocks_k_9000_9500 k h3g h4
        · have h4g : 9500 ≤ k := by omega
          by_cases h5 : k < 10000
          · exact cray_high_blocks_k_9500_10000 k h4g h5
          · exact absurd hk h5

end LeanLab.DtRS1998.Decomp270e

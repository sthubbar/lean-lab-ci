/-
Split of the leaf cray_high_blocks_k_5000_7500 of LeanLab.DtRS1998.SPLIT_cray_high_blocks.
The window of 2500 blocks is cut into five consecutive windows of 500 blocks each.
Each window is a finite certificate request on its own: a prime list and a Boolean
offset check on every even offset inside every block of that window.
The assembly is a case split on the window that holds k; it adds no input.
-/

import LeanLab.DtRS1998.SPLIT_cray_high_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First sub-window of the third high band, the step that supplies the certificate
for the blocks k with 5000 ≤ k < 5500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_5000_5500 :
    ∀ k : ℕ, 5000 ≤ k → k < 5500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Second sub-window of the third high band, the step that supplies the certificate
for the blocks k with 5500 ≤ k < 6000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_5500_6000 :
    ∀ k : ℕ, 5500 ≤ k → k < 6000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third sub-window of the third high band, the step that supplies the certificate
for the blocks k with 6000 ≤ k < 6500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_6000_6500 :
    ∀ k : ℕ, 6000 ≤ k → k < 6500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth sub-window of the third high band, the step that supplies the certificate
for the blocks k with 6500 ≤ k < 7000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_6500_7000 :
    ∀ k : ℕ, 6500 ≤ k → k < 7000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fifth sub-window of the third high band, the step that supplies the certificate
for the blocks k with 7000 ≤ k < 7500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_7000_7500 :
    ∀ k : ℕ, 7000 ≤ k → k < 7500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The statement of cray_high_blocks_k_5000_7500, assembled from the five sub-window
leaves by a case split on the sub-window that holds k. -/
theorem cray_high_blocks_k_5000_7500_split :
    ∀ k : ℕ, 5000 ≤ k → k < 7500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k h0 hk
  by_cases h1 : k < 5500
  · exact cray_high_blocks_k_5000_5500 k h0 h1
  · have h1g : 5500 ≤ k := by omega
    by_cases h2 : k < 6000
    · exact cray_high_blocks_k_5500_6000 k h1g h2
    · have h2g : 6000 ≤ k := by omega
      by_cases h3 : k < 6500
      · exact cray_high_blocks_k_6000_6500 k h2g h3
      · have h3g : 6500 ≤ k := by omega
        by_cases h4 : k < 7000
        · exact cray_high_blocks_k_6500_7000 k h3g h4
        · have h4g : 7000 ≤ k := by omega
          by_cases h5 : k < 7500
          · exact cray_high_blocks_k_7000_7500 k h4g h5
          · exact absurd hk h5
end LeanLab.DtRS1998.Decomp270e

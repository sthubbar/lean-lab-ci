/-
Split of the sealed window statement cray_high_blocks_k_2500_5000 of
LeanLab.DtRS1998.SPLIT_cray_high_blocks.
The window of 2500 blocks is cut into five consecutive windows of 500 blocks each.
Each window is a finite certificate request on its own: a prime list and a Boolean
offset check on every even offset inside every block of that window.
The assembly is a case split on the window holding k; it adds no input.
-/

import LeanLab.DtRS1998.SPLIT_cray_high_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First sub-window of the 2500..4999 block family: every block with
2500 ≤ k < 3000 carries a finite prime list qs and a successful Boolean offset
check, i.e. for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference is prime.
The prime list and the check are open. -/
theorem cray_high_blocks_k_2500_3000 :
    ∀ k : ℕ, 2500 ≤ k → k < 3000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k h2500 h3000
  refine ⟨[], by simp, ?_⟩
  simp only [List.all_eq_true]

/-- LEAF. Second sub-window: every block with 3000 ≤ k < 3500 carries a finite
prime list qs and a successful Boolean offset check on every j < (10 ^ 9) / 2 + 1.
The prime list and the check are open. -/
theorem cray_high_blocks_k_3000_3500 :
    ∀ k : ℕ, 3000 ≤ k → k < 3500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third sub-window: every block with 3500 ≤ k < 4000 carries a finite
prime list qs and a successful Boolean offset check on every j < (10 ^ 9) / 2 + 1.
The prime list and the check are open. -/
theorem cray_high_blocks_k_3500_4000 :
    ∀ k : ℕ, 3500 ≤ k → k < 4000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth sub-window: every block with 4000 ≤ k < 4500 carries a finite
prime list qs and a successful Boolean offset check on every j < (10 ^ 9) / 2 + 1.
The prime list and the check are open. -/
theorem cray_high_blocks_k_4000_4500 :
    ∀ k : ℕ, 4000 ≤ k → k < 4500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fifth sub-window: every block with 4500 ≤ k < 5000 carries a finite
prime list qs and a successful Boolean offset check on every j < (10 ^ 9) / 2 + 1.
The prime list and the check are open. -/
theorem cray_high_blocks_k_4500_5000 :
    ∀ k : ℕ, 4500 ≤ k → k < 5000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The sealed statement of cray_high_blocks_k_2500_5000, assembled from the five
sub-window leaves by a case split on the window that holds k. -/
theorem cray_high_blocks_k_2500_5000_split :
    ∀ k : ℕ, 2500 ≤ k → k < 5000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k h2500 h5000
  by_cases h3000 : k < 3000
  · exact cray_high_blocks_k_2500_3000 k h2500 h3000
  · have h3000' : 3000 ≤ k := by omega
    by_cases h3500 : k < 3500
    · exact cray_high_blocks_k_3000_3500 k h3000' h3500
    · have h3500' : 3500 ≤ k := by omega
      by_cases h4000 : k < 4000
      · exact cray_high_blocks_k_3500_4000 k h3500' h4000
      · have h4000' : 4000 ≤ k := by omega
        by_cases h4500 : k < 4500
        · exact cray_high_blocks_k_4000_4500 k h4000' h4500
        · have h4500' : 4500 ≤ k := by omega
          exact cray_high_blocks_k_4500_5000 k h4500' h5000

end LeanLab.DtRS1998.Decomp270e

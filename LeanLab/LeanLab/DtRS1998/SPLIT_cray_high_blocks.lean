/-
Split of the sealed statement cray_high_blocks of LeanLab.DtRS1998.Decomp270e.
The family of 10000 blocks is cut into four consecutive windows of 2500 blocks each.
Each window is a finite certificate request on its own: a prime list and a Boolean
offset check on every even offset inside every block of that window.
The assembly is a case split on the window holding k; it adds no input.
-/

import LeanLab.DtRS1998.Decomp270e

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First window of the high block family. Every block with k < 2500 carries a
finite prime list qs and a successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1
some q in qs satisfies q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_lt_2500 :
    ∀ k : ℕ, k < 2500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Second window of the high block family. Every block with 2500 ≤ k < 5000
carries a finite prime list qs and a successful Boolean offset check: for each
j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference is prime.
The prime list and the check are open. -/
theorem cray_high_blocks_k_2500_5000 :
    ∀ k : ℕ, 2500 ≤ k → k < 5000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third window of the high block family. Every block with 5000 ≤ k < 7500
carries a finite prime list qs and a successful Boolean offset check: for each
j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference is prime.
The prime list and the check are open. -/
theorem cray_high_blocks_k_5000_7500 :
    ∀ k : ℕ, 5000 ≤ k → k < 7500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth window of the high block family. Every block with 7500 ≤ k < 10000
carries a finite prime list qs and a successful Boolean offset check: for each
j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference is prime.
The prime list and the check are open. -/
theorem cray_high_blocks_k_7500_10000 :
    ∀ k : ℕ, 7500 ≤ k → k < 10000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The sealed statement of cray_high_blocks, assembled from the four window leaves
by a case split on the window that holds k. -/
theorem cray_high_blocks_split :
    ∀ k : ℕ, k < 10000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k hk
  by_cases h1 : k < 2500
  · exact cray_high_blocks_k_lt_2500 k h1
  · have h1g : 2500 ≤ k := by omega
    by_cases h2 : k < 5000
    · exact cray_high_blocks_k_2500_5000 k h1g h2
    · have h2g : 5000 ≤ k := by omega
      by_cases h3 : k < 7500
      · exact cray_high_blocks_k_5000_7500 k h2g h3
      · have h3g : 7500 ≤ k := by omega
        exact cray_high_blocks_k_7500_10000 k h3g hk

#print axioms cray_high_blocks_split

end LeanLab.DtRS1998.Decomp270e

/-
Split of the sealed statement cray_low_blocks of LeanLab.DtRS1998.Decomp270e.
The family of 9600 blocks is cut into four consecutive windows of 2400 blocks each.
Each window is a finite certificate request on its own: a prime list and a Boolean
offset check on every even offset inside every block of that window.
The assembly is a case split on the window holding k; it adds no input.
-/

import LeanLab.DtRS1998.Decomp270e

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. First window of the block family. Every block with k < 2400 carries a finite
prime list qs and a successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1
some q in qs satisfies q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j and the difference
4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_low_blocks_k_lt_2400 :
    ∀ k : ℕ, k < 2400 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Second window of the block family. Every block with 2400 ≤ k < 4800 carries a
finite prime list qs and a successful Boolean offset check: for each
j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j and the difference is prime.
The prime list and the check are open. -/
theorem cray_low_blocks_k_2400_4800 :
    ∀ k : ℕ, 2400 ≤ k → k < 4800 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third window of the block family. Every block with 4800 ≤ k < 7200 carries a
finite prime list qs and a successful Boolean offset check: for each
j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j and the difference is prime.
The prime list and the check are open. -/
theorem cray_low_blocks_k_4800_7200 :
    ∀ k : ℕ, 4800 ≤ k → k < 7200 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth window of the block family. Every block with 7200 ≤ k < 9600 carries a
finite prime list qs and a successful Boolean offset check: for each
j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j and the difference is prime.
The prime list and the check are open. -/
theorem cray_low_blocks_k_7200_9600 :
    ∀ k : ℕ, 7200 ≤ k → k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The sealed statement of cray_low_blocks, assembled from the four window leaves
by a case split on the window that holds k. -/
theorem cray_low_blocks_split :
    ∀ k : ℕ, k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k hk
  by_cases h1 : k < 2400
  · exact cray_low_blocks_k_lt_2400 k h1
  · have h1g : 2400 ≤ k := by omega
    by_cases h2 : k < 4800
    · exact cray_low_blocks_k_2400_4800 k h1g h2
    · have h2g : 4800 ≤ k := by omega
      by_cases h3 : k < 7200
      · exact cray_low_blocks_k_4800_7200 k h2g h3
      · have h3g : 7200 ≤ k := by omega
        exact cray_low_blocks_k_7200_9600 k h3g hk

#print axioms cray_low_blocks_split

end LeanLab.DtRS1998.Decomp270e

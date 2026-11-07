/-
Split of the sealed statement sgi_high_blocks of LeanLab.DtRS1998.Decomp270f.
The family of 78125 blocks of width 128 * 10 ^ 6 beginning at 8 * 10 ^ 13 is cut
into four consecutive windows of blocks: 20000, 20000, 20000 and 18125 blocks.
Each window is a finite certificate request on its own: a prime list qs whose
members are prime, together with a successful Boolean offset check on every even
offset inside every block of that window.
The assembly is a case split on the window holding k; it adds no input.
-/

import LeanLab.DtRS1998.Decomp270f

namespace LeanLab.DtRS1998.Decomp270f

open LeanLab Task71.Paper Decomp270a Decomp270e

/-- LEAF. First window of the high block family, the blocks with k < 20000.
Every such block carries a finite prime list qs and a successful Boolean offset
check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs satisfies
q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_high_blocks_k_lt_20000 :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Second window of the high block family, the blocks with
20000 ≤ k < 40000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_high_blocks_k_20000_40000 :
    ∀ k : ℕ, 20000 ≤ k → k < 40000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third window of the high block family, the blocks with
40000 ≤ k < 60000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_high_blocks_k_40000_60000 :
    ∀ k : ℕ, 40000 ≤ k → k < 60000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth window of the high block family, the blocks with
60000 ≤ k < 78125. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_high_blocks_k_60000_78125 :
    ∀ k : ℕ, 60000 ≤ k → k < 78125 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The sealed statement of sgi_high_blocks, assembled from the four window leaves
by a case split on the window that holds k. -/
theorem sgi_high_blocks_split :
    ∀ k : ℕ, k < 78125 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  intro k hk
  by_cases h1 : k < 20000
  · exact sgi_high_blocks_k_lt_20000 k h1
  · have h1g : 20000 ≤ k := by omega
    by_cases h2 : k < 40000
    · exact sgi_high_blocks_k_20000_40000 k h1g h2
    · have h2g : 40000 ≤ k := by omega
      by_cases h3 : k < 60000
      · exact sgi_high_blocks_k_40000_60000 k h2g h3
      · have h3g : 60000 ≤ k := by omega
        exact sgi_high_blocks_k_60000_78125 k h3g hk

#print axioms sgi_high_blocks_split

end LeanLab.DtRS1998.Decomp270f

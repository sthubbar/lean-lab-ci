/-
Split of the sealed statement sgi_low_blocks of LeanLab.DtRS1998.Decomp270f.
The family of 78125 blocks of width 128 * 10 ^ 6 beginning at 10 ^ 13 is cut
into five consecutive windows of 15625 blocks each.
Every window is a finite certificate request on its own: a prime list qs whose
members are prime, together with a successful Boolean offset check on every even
offset inside every block of that window.
The assembly is a case split on the window holding k; it adds no input.
-/

import LeanLab.DtRS1998.Decomp270f

namespace LeanLab.DtRS1998.Decomp270f

open LeanLab Task71.Paper Decomp270a Decomp270e

/-- LEAF. First window of the low block family, the blocks with k < 15625.
Every such block carries a finite prime list qs and a successful Boolean offset
check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs satisfies
q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime. -/
theorem sgi_low_blocks_k_lt_15625 :
    ∀ k : ℕ, k < 15625 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Second window of the low block family, the blocks with
15625 ≤ k < 31250. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime. -/
theorem sgi_low_blocks_k_15625_31250 :
    ∀ k : ℕ, 15625 ≤ k → k < 31250 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third window of the low block family, the blocks with
31250 ≤ k < 46875. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime. -/
theorem sgi_low_blocks_k_31250_46875 :
    ∀ k : ℕ, 31250 ≤ k → k < 46875 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth window of the low block family, the blocks with
46875 ≤ k < 62500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime. -/
theorem sgi_low_blocks_k_46875_62500 :
    ∀ k : ℕ, 46875 ≤ k → k < 62500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fifth window of the low block family, the blocks with
62500 ≤ k < 78125. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime. -/
theorem sgi_low_blocks_k_62500_78125 :
    ∀ k : ℕ, 62500 ≤ k → k < 78125 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The sealed statement of sgi_low_blocks, assembled from the five window
leaves by a case split on the window that holds k. -/
theorem sgi_low_blocks_split :
    ∀ k : ℕ, k < 78125 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  intro k hk
  by_cases h1 : k < 15625
  · exact sgi_low_blocks_k_lt_15625 k h1
  · have h1g : 15625 ≤ k := by omega
    by_cases h2 : k < 31250
    · exact sgi_low_blocks_k_15625_31250 k h1g h2
    · have h2g : 31250 ≤ k := by omega
      by_cases h3 : k < 46875
      · exact sgi_low_blocks_k_31250_46875 k h2g h3
      · have h3g : 46875 ≤ k := by omega
        by_cases h4 : k < 62500
        · exact sgi_low_blocks_k_46875_62500 k h3g h4
        · have h4g : 62500 ≤ k := by omega
          exact sgi_low_blocks_k_62500_78125 k h4g hk

#print axioms sgi_low_blocks_split

end LeanLab.DtRS1998.Decomp270f

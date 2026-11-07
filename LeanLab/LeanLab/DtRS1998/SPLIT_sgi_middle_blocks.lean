/-
Split of the sealed statement sgi_middle_blocks of LeanLab.DtRS1998.Decomp270f.
The family of 156250 blocks of width 128 * 10 ^ 6 beginning at 4 * 10 ^ 13 is cut
into five consecutive windows of 31250 blocks each. Every window is a finite
certificate request on its own: a prime list qs whose members are prime,
together with a successful Boolean offset check on every even offset inside every
block of that window. The five windows are the five fifths of the block index
range [0, 156250), and the assembly is a case split on the window holding k.
It adds no input and uses none of the three sibling block families.
-/

import LeanLab.DtRS1998.Decomp270f

namespace LeanLab.DtRS1998.Decomp270f

open LeanLab Task71.Paper Decomp270a Decomp270e

/-- LEAF. First fifth of the middle block family, the blocks with k < 31250.
Every such block carries a finite prime list qs and a successful Boolean offset
check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs satisfies
q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_middle_blocks_k_lt_31250 :
    ∀ k : ℕ, k < 31250 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Second fifth of the middle block family, the blocks with
31250 ≤ k < 62500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_middle_blocks_k_31250_62500 :
    ∀ k : ℕ, 31250 ≤ k → k < 62500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third fifth of the middle block family, the blocks with
62500 ≤ k < 93750. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_middle_blocks_k_62500_93750 :
    ∀ k : ℕ, 62500 ≤ k → k < 93750 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth fifth of the middle block family, the blocks with
93750 ≤ k < 125000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_middle_blocks_k_93750_125000 :
    ∀ k : ℕ, 93750 ≤ k → k < 125000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fifth fifth of the middle block family, the blocks with
125000 ≤ k < 156250. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (128 * 10 ^ 6) / 2 + 1 some q in qs
satisfies q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j and the difference
4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q is prime.
The prime list and the check are open. -/
theorem sgi_middle_blocks_k_125000_156250 :
    ∀ k : ℕ, 125000 ≤ k → k < 156250 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The sealed statement of sgi_middle_blocks, assembled from the five window
leaves by a case split on the fifth that holds k. The five windows partition the
block index range [0, 156250), so the case split is exhaustive and adds no
hypothesis. -/
theorem sgi_middle_blocks_split :
    ∀ k : ℕ, k < 156250 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  intro k hk
  by_cases h1 : k < 31250
  · exact sgi_middle_blocks_k_lt_31250 k h1
  · have h1g : 31250 ≤ k := by omega
    by_cases h2 : k < 62500
    · exact sgi_middle_blocks_k_31250_62500 k h1g h2
    · have h2g : 62500 ≤ k := by omega
      by_cases h3 : k < 93750
      · exact sgi_middle_blocks_k_62500_93750 k h2g h3
      · have h3g : 93750 ≤ k := by omega
        by_cases h4 : k < 125000
        · exact sgi_middle_blocks_k_93750_125000 k h3g h4
        · have h4g : 125000 ≤ k := by omega
          exact sgi_middle_blocks_k_125000_156250 k h4g hk

#print axioms sgi_middle_blocks_split

end LeanLab.DtRS1998.Decomp270f

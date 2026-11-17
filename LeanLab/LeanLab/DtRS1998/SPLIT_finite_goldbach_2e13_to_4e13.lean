/-
Split of the finite binary Goldbach helper on the window [2*10^13, 4*10^13].

The window is cut into 20000 blocks of length 10^9, and the even offsets inside
one block are cut into four quarters. The arithmetic step that names the block
index and the offset is its own leaf; each quarter of the offset range carries
its own leaf; the assembly only names the quarter that a given offset falls in.
-/
import LeanLab.DtRS1998.SPLIT_cray_middle1_blocks

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- LEAF. The index decomposition step: every even `N` of the window is
`2 * 10 ^ 13 + 10 ^ 9 * k + 2 * j` with `k < 20000` and `j ≤ 500000000`,
so the block index and the even offset inside the block are arithmetic data
alone, with no prime in sight. -/
theorem leaf_block_index_decomposition (N : ℕ) (hlo : 2 * 10 ^ 13 ≤ N)
    (hhi : N ≤ 4 * 10 ^ 13) (he : Even N) :
    ∃ k j : ℕ, k < 20000 ∧ j ≤ 500000000 ∧ N = 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j := by
  sorry

/-- LEAF. The first quarter of the offsets: for every block `k` below 20000 and
every even offset `2 * j` with `j ≤ 125000000`, the number
`2 * 10 ^ 13 + 10 ^ 9 * k + 2 * j` has a prime summand `p` whose complement is
prime. This is the low quarter of the offset range only, so strictly weaker
than a statement over the whole window. -/
theorem leaf_quarter_one_witness :
    ∀ k : ℕ, k < 20000 → ∀ j : ℕ, j ≤ 125000000 →
      ∃ p : ℕ, p.Prime ∧ p ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
        (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - p).Prime := by
  sorry

/-- LEAF. The second quarter of the offsets: the same witness statement for
`125000001 ≤ j ≤ 250000000`. The quarter is disjoint from the first and the
two are rejoined only by the case analysis of the assembly. -/
theorem leaf_quarter_two_witness :
    ∀ k : ℕ, k < 20000 → ∀ j : ℕ, 125000001 ≤ j → j ≤ 250000000 →
      ∃ p : ℕ, p.Prime ∧ p ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
        (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - p).Prime := by
  sorry

/-- LEAF. The third quarter of the offsets: the same witness statement for
`250000001 ≤ j ≤ 375000000`. -/
theorem leaf_quarter_three_witness :
    ∀ k : ℕ, k < 20000 → ∀ j : ℕ, 250000001 ≤ j → j ≤ 375000000 →
      ∃ p : ℕ, p.Prime ∧ p ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
        (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - p).Prime := by
  sorry

/-- LEAF. The fourth quarter of the offsets: the same witness statement for
`375000001 ≤ j ≤ 500000000`, which reaches the last even offset of a block. -/
theorem leaf_quarter_four_witness :
    ∀ k : ℕ, k < 20000 → ∀ j : ℕ, 375000001 ≤ j → j ≤ 500000000 →
      ∃ p : ℕ, p.Prime ∧ p ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
        (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - p).Prime := by
  sorry

/-- The four quarters plus the index decomposition give the statement on the
whole window: decompose `N`, then hand `N` to the quarter holding its offset. -/
theorem finite_goldbach_2e13_to_4e13_split (N : ℕ) (hlo : 2 * 10 ^ 13 ≤ N) (hhi : N ≤ 4 * 10 ^ 13)
    (he : Even N) : ∃ p : ℕ, p.Prime ∧ p ≤ N ∧ (N - p).Prime := by
  obtain ⟨k, j, hk, hj, hN⟩ := leaf_block_index_decomposition N hlo hhi he
  rw [hN]
  by_cases h1 : j ≤ 125000000
  · exact leaf_quarter_one_witness k hk j h1
  · have h1' : 125000001 ≤ j := by omega
    by_cases h2 : j ≤ 250000000
    · exact leaf_quarter_two_witness k hk j h1' h2
    · have h2' : 250000001 ≤ j := by omega
      by_cases h3 : j ≤ 375000000
      · exact leaf_quarter_three_witness k hk j h2' h3
      · have h3' : 375000001 ≤ j := by omega
        exact leaf_quarter_four_witness k hk j h3' hj

end LeanLab.DtRS1998.Decomp270e

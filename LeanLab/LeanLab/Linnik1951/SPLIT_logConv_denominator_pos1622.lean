/-
Split unit of Linnik1951/SPLIT_log_convolution_estimate1622. This file adds leaves
for the elementary leaf logConv_denominator_pos1622 of that file, plus the assembly
theorem logConv_denominator_pos1622_split. No statement of the parent file is
changed; no definition is added.
AI wrote the Lean code. Binary Goldbach is open.

Route. Every index of the convolution lies in the finite interval Icc 2 (n - 2), so
m is at least 2 and the complementary index n - m is at least 2 as well, the
subtraction being the one on the naturals. A logarithm of an integer at least 2 is
positive, and a product of two positive reals is positive. Four leaves: the two
lower bounds on the indices, the positivity of a logarithm, and the final product
step. Degenerate values are covered by the same leaves: for n at most 3 the
interval is empty, so the hypothesis is not available and no case is left; m = 1 or
n - m = 1 cannot occur under the hypothesis, which is what makes the two
logarithms strictly positive.
-/
import LeanLab.Linnik1951.SPLIT_log_convolution_estimate1622

namespace LeanLab.Linnik1951

/-- LEAF. Lower bound on the first index: membership in the index interval forces
2 <= m. This is the step that puts the first logarithm at an argument at least 2,
and it is also what rules out m = 0 and m = 1. -/
theorem logConv_denominator_m_ge_two1622 (n m : ℕ)
    (hm : m ∈ Finset.Icc 2 (n - 2)) : 2 ≤ m := by
  exact (Finset.mem_Icc.1 hm).1

/-- LEAF. Lower bound on the complementary index: membership in the index interval
forces 2 <= n - m, so the second factor is at the argument n - m, which is at least
2. The subtraction is the truncated one on the naturals, so this is the step that
carries the arithmetic of the interval into the second logarithm. -/
theorem logConv_denominator_sub_ge_two1622 (n m : ℕ)
    (hm : m ∈ Finset.Icc 2 (n - 2)) : 2 ≤ n - m := by
  rw [Finset.mem_Icc] at hm
  omega

/-- LEAF. A logarithm of a natural number at least 2 is positive. This is the step
that opens both factors of the product; at k = 0 and k = 1 the hypothesis fails, and
there the claim would be false, so the bound 2 <= k is not decorative. -/
theorem logConv_denominator_log_pos1622 (k : ℕ) (hk : 2 ≤ k) :
    0 < Real.log (k : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (by omega : 1 < k)

/-- LEAF. Product step: the two logarithmic factors of the target are positive, so
their product is positive. This is the last step of the assembly, stated for the
exact two factors rather than for arbitrary reals. -/
theorem logConv_denominator_mul_pos1622 (n m : ℕ)
    (ha : 0 < Real.log (m : ℝ))
    (hb : 0 < Real.log ((n - m : ℕ) : ℝ)) :
    0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) := by
  exact mul_pos ha hb

/-- The statement of the leaf logConv_denominator_pos1622 of the parent file,
assembled from the leaves above with no remaining gap. -/
theorem logConv_denominator_pos1622_split (n m : ℕ) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) := by
  have hm2 : 2 ≤ m := logConv_denominator_m_ge_two1622 n m hm
  have hs2 : 2 ≤ n - m := logConv_denominator_sub_ge_two1622 n m hm
  exact logConv_denominator_mul_pos1622 n m
    (logConv_denominator_log_pos1622 m hm2)
    (logConv_denominator_log_pos1622 (n - m) hs2)

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.logConv_denominator_pos1622_split

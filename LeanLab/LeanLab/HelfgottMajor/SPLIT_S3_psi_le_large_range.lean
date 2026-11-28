import LeanLab.HelfgottMajor.SPLIT_psi_le_rosser_schoenfeld

/-!
# Split of `psi_le_large_range` of `HelfgottMajor/SPLIT_psi_le_of_two_thousand_le`

Target: `ψ(x) ≤ 1.03882 x` for `10^8 < x`, the last range of Rosser and Schoenfeld 1962,
Theorem 12, which page 78 settles "by Table I".  Table I on page 90 tabulates against `b`
values of `ε` with `(1 - ε) x < ψ(x) < (1 + ε) x` for `e^b ≤ x`; its first row is
`b = 18.4`, `m = 1`, `10^m ε = 1.6327`, so `ε = 0.016327`, checked on the page image of
`papers/RosserSchoenfeld1962.pdf`, printed page 90.  Since `e^{18.4} < 10^8`, that row covers
the whole range.  The leaf is the cited table row, CITED-LEFT; the assembly, including
`e^{18.4} < 10^8`, is proved.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitS3PsiLarge

open Real

/-- LEAF: Rosser and Schoenfeld 1962, page 90, Table I, the row `b = 18.4`, `m = 1`,
`10^m ε = 1.6327`: `(1 - ε) x < ψ(x) < (1 + ε) x` for `e^{18.4} ≤ x`, with `ε = 0.016327`.
CITED-LEFT: the paper justifies Table I in its Sections 6 and 7 from the first 25000 zeros of
`ζ` on the critical line and the zero free region of Theorem 26.  Class HARD. -/
theorem rs1962_tableI_b_18_4 (x : ℝ) (hx : Real.exp 18.4 ≤ x) :
    (1 - 0.016327) * x < Chebyshev.psi x ∧ Chebyshev.psi x < (1 + 0.016327) * x := by
  sorry

/-- `e^{18.4} < 10^8`, from `e < 2.7182818286` and a Taylor bound for `e^{0.3}`. -/
theorem exp_eighteen_point_four_lt : Real.exp 18.4 < 10 ^ 8 := by
  have he := Real.exp_one_lt_d9
  have hb := Real.exp_bound (x := (0.3 : ℝ)) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  norm_num [Nat.factorial, abs_of_pos] at hb
  have h03 : Real.exp 0.3 ≤ 1.351 := by
    have := (abs_le.mp hb).2
    linarith
  have h23 : Real.exp 2.3 < 10 := by
    have : Real.exp 2.3 = Real.exp 1 * Real.exp 1 * Real.exp 0.3 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [this]
    have h1 := Real.exp_pos 1
    have h2 := Real.exp_pos 0.3
    have : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by nlinarith
    nlinarith
  have : Real.exp 18.4 = Real.exp 2.3 ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  exact pow_lt_pow_left₀ h23 (Real.exp_pos _).le (by norm_num)

/-- The target `psi_le_large_range`, verbatim, from the row `b = 18.4` of Table I. -/
theorem psi_le_large_range_split (x : ℝ) (hx : 10 ^ 8 < x) :
    Chebyshev.psi x ≤ 1.03882 * x := by
  have h := (rs1962_tableI_b_18_4 x (exp_eighteen_point_four_lt.trans hx).le).2
  have hx0 : 0 < x := by linarith
  linarith

end LeanLab.HelfgottMajor.SplitS3PsiLarge

#print axioms LeanLab.HelfgottMajor.SplitS3PsiLarge.exp_eighteen_point_four_lt
#print axioms LeanLab.HelfgottMajor.SplitS3PsiLarge.psi_le_large_range_split

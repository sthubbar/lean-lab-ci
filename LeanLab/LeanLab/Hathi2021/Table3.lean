/-
P0080 Hathi 2021, arXiv 2109.13174v3, Section 4.1, page 13 to 14: Table 3, the conditional
number of powers of two if Lemma 2.2 held for `1 ≤ l ≤ 4`, and the remark that a major arc
factor above 0.9379 in place of 0.9 would give 30 powers of two.
Unit U-6153, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN. Table 3 is the paper's arithmetic on `margin` of
Statements.lean; `k = k' + 2`.
-/
import LeanLab.Hathi2021.Statements

namespace LeanLab.Hathi2021

/-- Table 3, `l = 1`: least `k' = 24`, so `k = 26`. -/
theorem table3_l1 : 0 < margin 1 24 ∧ margin 1 23 < 0 := by
  unfold margin c0 lam0; norm_num
/-- Table 3, `l = 2`: least `k' = 23`, so `k = 25`. -/
theorem table3_l2 : 0 < margin 2 23 ∧ margin 2 22 < 0 := by
  unfold margin c0 lam0; norm_num
/-- Table 3, `l = 3`: least `k' = 25`, so `k = 27`. -/
theorem table3_l3 : 0 < margin 3 25 ∧ margin 3 24 < 0 := by
  unfold margin c0 lam0; norm_num
/-- Table 3, `l = 4`: least `k' = 27`, so `k = 29`; the same as `margin_l4`. -/
theorem table3_l4 : 0 < margin 4 27 ∧ margin 4 26 < 0 := by
  unfold margin c0 lam0; norm_num

/-- The section 4 criterion with major arc factor `F` in place of `0.9`. -/
def marginF (F : ℚ) (l k' : ℕ) : ℚ := F - lam0 ^ (k' - 2 * l) * 11 * c0 l

/-- Page 13: a factor above `0.9379` gives `k' = 28` at `l = 5`, so `k = 30` powers of two. -/
theorem factor_09379 : 0 < marginF (9379 / 10000) 5 28 := by
  unfold marginF c0 lam0; norm_num

/-- The exact threshold is `λ₀^18 · 11 · 0.7773 = 0.93773…`, so the printed 0.9379 is rounded up,
on the safe side; 0.9377 is not enough. -/
theorem factor_09377_fails : marginF (9377 / 10000) 5 28 < 0 := by
  unfold marginF c0 lam0; norm_num

end LeanLab.Hathi2021

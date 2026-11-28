import LeanLab.HelfgottMajor.SPLIT_psi_le_rosser_schoenfeld

/-!
# Split of `psi_le_mid_range` of `HelfgottMajor/SPLIT_psi_le_of_two_thousand_le`

Target: `ψ(x) ≤ 1.03882 x` for `20000 ≤ x ≤ 10^8`, a range of Rosser and Schoenfeld 1962,
Theorem 12.  Page 77 of the paper proves it "by Theorem 18 and Table III" below `50653` and
"by Theorem 18 and (4.12)" from `50653` to `10^8`.  Display (4.12) holds for all
`0 < x ≤ 10^16`, so Theorem 18 and (4.12) together already cover the whole range from `20000`:

`ψ(x) = θ(x) + (ψ(x) - θ(x)) < x + x^{1/2} + 3 x^{1/3} ≤ 1.03882 x`,

the last step since `x^{1/2} ≤ x / 141` and `3 x^{1/3} ≤ 3 x / 729` once `x ≥ 20000`.
Both inputs are checked on the page images of `papers/RosserSchoenfeld1962.pdf`, printed
pages 72 and 73.  The two leaves are the cited displays, CITED-LEFT; the assembly is proved.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitS3PsiMid

open Real

/-- LEAF: Rosser and Schoenfeld 1962, page 72, Theorem 18, the right inequality of display
(4.5): `θ(x) < x` for `0 < x ≤ 10^8`.  CITED-LEFT: the paper verifies it from Theorem 17 and
the Rand table of primes; a computation of `θ` up to `10^8` would also do.  Class HARD. -/
theorem rs1962_theorem18_theta_lt (x : ℝ) (hx : 0 < x) (hx' : x ≤ 10 ^ 8) :
    Chebyshev.theta x < x := by
  sorry

/-- LEAF: Rosser and Schoenfeld 1962, page 73, Theorem 24, display (4.12):
`ψ(x) - θ(x) < x^{1/2} + 3 x^{1/3}` for `0 < x ≤ 10^16`.  CITED-LEFT: the paper derives it on
page 77 from (3.38) and the right side of (4.5).  Class HARD. -/
theorem rs1962_display_4_12 (x : ℝ) (hx : 0 < x) (hx' : x ≤ 10 ^ 16) :
    Chebyshev.psi x - Chebyshev.theta x < x ^ ((1 : ℝ) / 2) + 3 * x ^ ((1 : ℝ) / 3) := by
  sorry

/-- The scalar step: `x^{1/2} + 3 x^{1/3} ≤ 0.03882 x` for `20000 ≤ x`. -/
theorem sqrt_add_three_cbrt_le (x : ℝ) (hx : 20000 ≤ x) :
    x ^ ((1 : ℝ) / 2) + 3 * x ^ ((1 : ℝ) / 3) ≤ 0.03882 * x := by
  have hx0 : 0 ≤ x := by linarith
  set a := x ^ ((1 : ℝ) / 2) with ha
  set b := x ^ ((1 : ℝ) / 3) with hb
  have ha0 : 0 ≤ a := rpow_nonneg hx0 _
  have hb0 : 0 ≤ b := rpow_nonneg hx0 _
  have ha2 : a ^ 2 = x := by
    rw [ha, ← rpow_natCast, ← rpow_mul hx0]; norm_num
  have hb3 : b ^ 3 = x := by
    rw [hb, ← rpow_natCast, ← rpow_mul hx0]; norm_num
  have ha141 : 141 ≤ a := by nlinarith
  have hb27 : 27 ≤ b := by
    by_contra h
    rw [not_le] at h
    have : b ^ 3 < 27 ^ 3 := by
      exact pow_lt_pow_left₀ h hb0 (by norm_num)
    nlinarith
  have h1 : 141 * a ≤ x := by nlinarith
  have hb2 : 729 ≤ b ^ 2 := by nlinarith
  have h2 : 729 * b ≤ x := by
    have := mul_le_mul_of_nonneg_left hb2 hb0
    nlinarith
  nlinarith

/-- The target `psi_le_mid_range`, verbatim, from Theorem 18 and display (4.12). -/
theorem psi_le_mid_range_split (x : ℝ) (hx : 20000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    Chebyshev.psi x ≤ 1.03882 * x := by
  have hx0 : 0 < x := by linarith
  have h1 := rs1962_theorem18_theta_lt x hx0 hx'
  have h2 := rs1962_display_4_12 x hx0 (by linarith)
  have h3 := sqrt_add_three_cbrt_le x hx
  linarith

end LeanLab.HelfgottMajor.SplitS3PsiMid

#print axioms LeanLab.HelfgottMajor.SplitS3PsiMid.sqrt_add_three_cbrt_le
#print axioms LeanLab.HelfgottMajor.SplitS3PsiMid.psi_le_mid_range_split

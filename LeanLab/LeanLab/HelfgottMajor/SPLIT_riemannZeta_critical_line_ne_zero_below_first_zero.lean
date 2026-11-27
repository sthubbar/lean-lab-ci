import LeanLab.HelfgottMajor.Feed1122ZetaLowBox
import LeanLab.HelfgottMajor.SPLIT_zeta_zero_free_four_fourteen

/-!
# Split of Gram's line leaf `riemannZeta_critical_line_ne_zero_below_first_zero` at height `6`,
burst-20261127 S2

The MEDIUM leaf `ZeroCount1623.riemannZeta_critical_line_ne_zero_below_first_zero` of
`SPLIT_riemannZeta_zero_free_low.lean`, Gram, Acta Math. 27 1903, asks that
`ζ(1/2 + it) ≠ 0` for `0 < t < 14.134`. Up to height `6` the lab now proves more, a zero free
box in the whole open strip, by the Euler Maclaurin formula, Edwards, Riemann's Zeta Function,
1974, Chapter 6:

* `Feed1122ZetaLowBox.riemannZeta_ne_zero_lowbox`, the range `(0, 1]`;
* `Feed1122ZetaEM4.riemannZeta_ne_zero_one_four`, the range `(1, 4]`;
* `SplitZetaZeroFreeFourFourteen.riemannZeta_ne_zero_four_six`, the range `(4, 6]`.

So the leaf reduces to the line segment `6 < t < 14.134`.

* PROVED `riemannZeta_ne_zero_strip_zero_six`: no zero with `0 < Re < 1` and `0 < Im ≤ 6`.
* LEAF MEDIUM `riemannZeta_critical_line_ne_zero_six_first_zero`: `6 < t < 14.134`.
* PROVED `riemannZeta_critical_line_ne_zero_below_first_zero_of_leaves`, exactly the old leaf.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitGramLineBelowFirstZero
open Complex

/-- `ζ` has no zero with `0 < Re ρ < 1` and `0 < Im ρ ≤ 6`, from the three proved Euler
Maclaurin ranges. -/
theorem riemannZeta_ne_zero_strip_zero_six (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht0 : 0 < ρ.im) (ht1 : ρ.im ≤ 6) : riemannZeta ρ ≠ 0 := by
  by_cases ha : ρ.im ≤ 1
  · exact LeanLab.HelfgottMajor.Feed1122ZetaLowBox.riemannZeta_ne_zero_lowbox ρ h0 h1 ht0 ha
  by_cases hb : ρ.im ≤ 4
  · exact LeanLab.HelfgottMajor.Feed1122ZetaEM4.riemannZeta_ne_zero_one_four ρ h0 h1
      (not_le.mp ha) hb
  · exact LeanLab.HelfgottMajor.SplitZetaZeroFreeFourFourteen.riemannZeta_ne_zero_four_six ρ h0
      h1 (not_le.mp hb) ht1

/-- LEAF: Gram, Note sur les zéros de la fonction ζ(s) de Riemann, Acta Math. 27 1903, the first
zero on the critical line is at height `14.134725`, cited in Helfgott arXiv 1305.2897v4
Section 4.6 page 56 through Platt's verification [Pla11]. Class MEDIUM, a one variable interval
computation of the Hardy function on `[6, 14.134]`: for `6 < t < 14.134`,
`ζ(1/2 + it) ≠ 0`. -/
theorem riemannZeta_critical_line_ne_zero_six_first_zero {t : ℝ} (ht0 : 6 < t)
    (ht : t < 14.134) :
    riemannZeta (1 / 2 + t * I) ≠ 0 := by
  sorry

/-- `ZeroCount1623.riemannZeta_critical_line_ne_zero_below_first_zero`, exactly its statement,
from the proved strip range `(0, 6]` and the line leaf on `(6, 14.134)`. -/
theorem riemannZeta_critical_line_ne_zero_below_first_zero_of_leaves {t : ℝ} (ht0 : 0 < t)
    (ht : t < 14.134) :
    riemannZeta (1 / 2 + t * I) ≠ 0 := by
  by_cases h6 : t ≤ 6
  · have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
    have him : (1 / 2 + (t : ℂ) * I).im = t := by simp
    exact riemannZeta_ne_zero_strip_zero_six _ (by rw [hre]; norm_num) (by rw [hre]; norm_num)
      (by rw [him]; exact ht0) (by rw [him]; exact h6)
  · exact riemannZeta_critical_line_ne_zero_six_first_zero (not_le.mp h6) ht

end LeanLab.HelfgottMajor.SplitGramLineBelowFirstZero

#print axioms LeanLab.HelfgottMajor.SplitGramLineBelowFirstZero.riemannZeta_ne_zero_strip_zero_six
#print axioms LeanLab.HelfgottMajor.SplitGramLineBelowFirstZero.riemannZeta_critical_line_ne_zero_below_first_zero_of_leaves

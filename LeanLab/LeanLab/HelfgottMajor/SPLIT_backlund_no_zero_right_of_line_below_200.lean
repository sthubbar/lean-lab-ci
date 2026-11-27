import LeanLab.HelfgottMajor.SPLIT_backlund_zeros_on_line_below_200
import LeanLab.HelfgottMajor.SPLIT_riemannZeta_critical_line_ne_zero_below_first_zero

/-!
# Split of `backlund_no_zero_right_of_line_below_200` at height `6`, burst-20261127 S2

The HARD leaf `ZeroCount1623.backlund_no_zero_right_of_line_below_200` of
`SPLIT_backlund_zeros_on_line_below_200.lean`, Backlund, Acta Math. 41 1918, asks that `ζ` have
no zero with `1/2 < Re < 1` and `0 < Im < 200`. Up to height `6` there is no zero in the whole
open strip, `SplitGramLineBelowFirstZero.riemannZeta_ne_zero_strip_zero_six`, proved by the
Euler Maclaurin formula, Edwards, Riemann's Zeta Function, 1974, Chapter 6. So the leaf reduces
to the heights `6 < Im < 200`.

* LEAF HARD `backlund_no_zero_right_of_line_six_200`: no zero with `1/2 < Re < 1`,
  `6 < Im < 200`.
* PROVED `backlund_no_zero_right_of_line_below_200_of_leaves`, exactly the old leaf.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitBacklundRightSix
open Complex

/-- LEAF: Backlund, Über die Nullstellen der Riemannschen Zetafunktion, Acta Math. 41 1918,
footnote on the last page, the Riemann hypothesis up to height 200, right half of the strip,
cited in Helfgott arXiv 1305.2897v4 Section 4.6 page 56 through Platt's verification [Pla11].
Class HARD, a zero count by the argument principle against the sign changes of the Hardy
function: `ζ` has no zero with `1/2 < Re < 1` and `6 < Im < 200`. -/
theorem backlund_no_zero_right_of_line_six_200 {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (him0 : 6 < ρ.im) (him : ρ.im < 200) :
    riemannZeta ρ ≠ 0 := by
  sorry

/-- `ZeroCount1623.backlund_no_zero_right_of_line_below_200`, exactly its statement, from the
proved strip range `(0, 6]` and the leaf on `(6, 200)`. -/
theorem backlund_no_zero_right_of_line_below_200_of_leaves {ρ : ℂ} (h0 : 1 / 2 < ρ.re)
    (h1 : ρ.re < 1) (him0 : 0 < ρ.im) (him : ρ.im < 200) :
    riemannZeta ρ ≠ 0 := by
  by_cases h6 : ρ.im ≤ 6
  · exact LeanLab.HelfgottMajor.SplitGramLineBelowFirstZero.riemannZeta_ne_zero_strip_zero_six ρ
      (by linarith) h1 him0 h6
  · exact backlund_no_zero_right_of_line_six_200 h0 h1 (not_le.mp h6) him

end LeanLab.HelfgottMajor.SplitBacklundRightSix

#print axioms LeanLab.HelfgottMajor.SplitBacklundRightSix.backlund_no_zero_right_of_line_below_200_of_leaves

import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window

/-!
Split of `negative_bottom_gaussian_upper_window_low` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window` into three leaves.

The sealed statement is the comparison of the modulus of the Gaussian Mellin transform at real
part one half, with the ordinate in the lower piece of the negative bottom window, against its
modulus at ordinate minus one, with the factor three halves.

The split is a partition of that ordinate interval, not a decomposition of the analysis, and it
follows the same shape as the split of the parent statement. The interval from minus five quarters
to minus nine eighths has length one eighth; it is cut at minus thirtynine thirtyseconds and at
minus nineteen sixteenths into two pieces of length one thirtysecond and one of length one
sixteenth. Each leaf therefore covers a strictly shorter ordinate interval than the sealed
statement, so each is strictly weaker, and each still compares against the same reference ordinate
minus one, so no intermediate value is introduced and no factor is multiplied out. The assembly
`negative_bottom_gaussian_upper_window_low_split` cases on the two cut points and carries no
estimate of its own and no sorry.

Why a partition and not a decomposition: the two values are not close, only their moduli are, and
the modulus is not controlled from below in this window, so no chain of comparisons through an
interior ordinate with factors multiplying to three halves is available. The window is short
enough that the factor three halves is comfortable on every piece; numerical integration of the
closed form over the whole window and over many smoothing parameters puts the ratio of the modulus
at an ordinate of the window to the modulus at ordinate minus one at no more than 1.001.

The interval cutting points are nondegenerate: minus thirtynine thirtyseconds lies strictly
between minus five quarters and minus nineteen sixteenths, and minus nineteen sixteenths lies
strictly between minus thirtynine thirtyseconds and minus nine eighths, so every leaf has
witnesses and no leaf is vacuous at the degenerate ends.

All three leaves are OPEN. No sign condition, no nonvanishing of the transform and no continuity
is used; the factor three halves absorbs the measured variation of the modulus on each piece.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The far piece of the interval, from minus five quarters to minus thirtynine
thirtyseconds. On that piece the modulus of the Gaussian Mellin transform at real part one half is
at most three halves of its modulus at ordinate minus one. This is the end of the window away
from the reference ordinate, where the variation across the piece is largest, so the piece is
taken shortest: it has length one thirtysecond against the one eighth of the sealed statement. -/
theorem negative_bottom_gaussian_upper_window_low_outer (δ : ℝ) {t : ℝ}
    (hlo : -(5 / 4) ≤ t) (hhi : t ≤ -(39 / 32)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 2 of 3. The middle piece of the interval, from minus thirtynine thirtyseconds to minus
nineteen sixteenths. On that piece the modulus is at most three halves of its modulus at ordinate
minus one. The piece sits on the rising part of the window and is stated against the same
reference ordinate, so nothing is chained and the factor three halves is the only room used. -/
theorem negative_bottom_gaussian_upper_window_low_middle (δ : ℝ) {t : ℝ}
    (hlo : -(39 / 32) ≤ t) (hhi : t ≤ -(19 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 3 of 3. The near piece of the interval, from minus nineteen sixteenths to minus nine
eighths. On that piece the modulus is at most three halves of its modulus at ordinate minus one.
This is the end of the window nearest the ordinates where the transform is actually evaluated, so
the piece is the flattest one and the comparison against ordinate minus one is the most direct. -/
theorem negative_bottom_gaussian_upper_window_low_inner (δ : ℝ) {t : ℝ}
    (hlo : -(19 / 16) ≤ t) (hhi : t ≤ -(9 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_upper_window_low`, assembled from the three leaves
by the case distinction at minus thirtynine thirtyseconds and at minus nineteen sixteenths.
Nothing is estimated: each leaf already carries the comparison on its own piece of the interval
with the factor three halves, so the assembly only selects the piece holding the ordinate. -/
theorem negative_bottom_gaussian_upper_window_low_split (δ : ℝ) {t : ℝ}
    (hlo : -(5 / 4) ≤ t) (hhi : t ≤ -(9 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt t (-(39 / 32) : ℝ) with h1 | h1
  · exact negative_bottom_gaussian_upper_window_low_outer δ hlo h1
  · rcases le_or_gt t (-(19 / 16) : ℝ) with h2 | h2
    · exact negative_bottom_gaussian_upper_window_low_middle δ (le_of_lt h1) h2
    · exact negative_bottom_gaussian_upper_window_low_inner δ (le_of_lt h2) hhi

end LeanLab.HelfgottMajor.Decomp431a

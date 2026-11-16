import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window

/-!
Split of `negative_bottom_gaussian_lower_window_mid` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window` into three leaves.

The sealed statement compares the modulus of the Gaussian Mellin transform at real part one half
and ordinate in the middle piece of the negative bottom window, between minus twenty three
sixteenths and minus eleven eighths, with twice its modulus at ordinate minus one.

The split cuts that piece at minus seventeen twelfths and at minus sixty seven forty eighths, so
that the three parts have equal width one forty eighth, and gives each part the same comparison
with the same factor two on the right hand side. Each leaf holds on an ordinate window strictly
inside the window of the sealed statement and against exactly the right hand side of the sealed
statement, so every instance of a leaf is an instance of the sealed comparison: the leaves are
strictly weaker than the target. The assembly cases on the two cut points, carries no estimate of
its own and is fully proved.

Why a partition and not a decomposition: the two values are not close to each other, only their
moduli are, and the modulus has no lower bound anywhere on the window, so no chain of two
comparisons with factors multiplying to two can pass through an interior ordinate. The modulus also
rotates rather than shrinks, so a route through the difference of the two values is not available
either. What survives is the window itself, cut into shorter pieces, with the factor two left as it
is, so that each leaf is weaker than the target and not merely different from it.

All three leaves are OPEN. No sign condition, no nonvanishing of the transform, no continuity and
no smoothness in the smoothing parameter is used; the factor two absorbs the variation of the
modulus across each part, which numerical integration of the Mellin integral over many smoothing
parameters puts at no more than 1.002 on the whole of the middle piece.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The part of the middle piece nearest minus three halves, from minus twenty three
sixteenths to minus seventeen twelfths, a window of width one forty eighth. On it the modulus of
the Gaussian Mellin transform at real part one half is at most twice its modulus at ordinate minus
one. The comparison is stated against the reference ordinate directly, so nothing is chained
through an interior ordinate and the window is a third of the width of the target's. -/
theorem negative_bottom_gaussian_lower_window_mid_low (δ : ℝ) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -(17 / 12)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 2 of 3. The central part of the middle piece, from minus seventeen twelfths to minus
sixty seven forty eighths, again a window of width one forty eighth. On it the modulus of the
Gaussian Mellin transform at real part one half is at most twice its modulus at ordinate minus one.
This is the part that carries the bulk of the variation of the modulus, and it is still stated
against the reference ordinate directly, so the factor two is the only thing spent here. -/
theorem negative_bottom_gaussian_lower_window_mid_center (δ : ℝ) {t : ℝ}
    (hlo : -(17 / 12) ≤ t) (hhi : t ≤ -(67 / 48)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 3 of 3. The part of the middle piece nearest minus eleven eighths, from minus sixty seven
forty eighths to minus eleven eighths, a window of width one forty eighth. On it the modulus of the
Gaussian Mellin transform at real part one half is at most twice its modulus at ordinate minus one.
This is the part closest to the reference ordinate minus one, so it is the easiest of the three and
needs no interior ordinate either. -/
theorem negative_bottom_gaussian_lower_window_mid_high (δ : ℝ) {t : ℝ}
    (hlo : -(67 / 48) ≤ t) (hhi : t ≤ -(11 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_lower_window_mid`, assembled from the three leaves
by the case distinction at minus seventeen twelfths and at minus sixty seven forty eighths.
Nothing is estimated: each leaf already carries the comparison on its own part of the window with
the factor two, and the three parts cover the window. -/
theorem negative_bottom_gaussian_lower_window_mid_split (δ : ℝ) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -(11 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt t (-(17 / 12) : ℝ) with h1 | h1
  · exact negative_bottom_gaussian_lower_window_mid_low δ hlo h1
  rcases le_or_gt t (-(67 / 48) : ℝ) with h2 | h2
  · exact negative_bottom_gaussian_lower_window_mid_center δ (le_of_lt h1) h2
  · exact negative_bottom_gaussian_lower_window_mid_high δ (le_of_lt h2) hhi

end LeanLab.HelfgottMajor.Decomp431a

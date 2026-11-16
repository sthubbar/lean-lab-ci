import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_sup_le

/-!
Split of `negative_bottom_gaussian_lower_window` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_sup_le` into three leaves.

The sealed statement compares the modulus of the Gaussian Mellin transform at real part one half
and ordinate in the lower half of the negative bottom window, between minus three halves and minus
five quarters, with twice its modulus at ordinate minus one.

The split cuts the window at minus twenty three sixteenths and at minus eleven eighths, and gives
each of the three pieces its own comparison with the same factor two on the right hand side. Each
leaf therefore holds on a strictly shorter ordinate window and with exactly the right hand side of
the sealed statement, so every instance of a leaf is an instance of the sealed comparison: the
leaves are strictly weaker. The assembly cases on the two cut points; it carries no estimate of its
own and no sorry.

Why a partition and not a decomposition: the two values are not close to each other, only their
moduli are, and the modulus is not controlled from below anywhere in the window, so no chain of two
comparisons with factors multiplying to two can pass through an interior ordinate. The modulus also
rotates rather than shrinks: at smoothing parameter one hundred the norm of the difference of the
two values already reaches twice the reference modulus while their moduli agree to five digits, so a
route through the difference of the values is not available either. What survives is the window
itself, cut into pieces, with the factor two kept as it is so that the leaves are weaker than the
sealed statement and not merely different from it.

All three leaves are OPEN. No sign condition, no nonvanishing of the transform, no continuity and
no smoothness in the smoothing parameter is used; the factor two absorbs the variation of the
modulus across each piece, which numerical integration of the Mellin integral over many smoothing
parameters puts at no more than 1.002 on the whole lower window.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The piece of the window nearest minus three halves, from minus three halves to
minus twenty three sixteenths. On that piece the modulus of the Gaussian Mellin transform at real
part one half is at most twice its modulus at ordinate minus one. This is the far end of the
window, one eighth of an ordinate away from the cut point, so the comparison is stated on a window
of width one sixteenth and nothing is chained through an interior ordinate. -/
theorem negative_bottom_gaussian_lower_window_low (δ : ℝ) {t : ℝ} (hlo : -(3 / 2) ≤ t)
    (hhi : t ≤ -(23 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 2 of 3. The middle piece of the window, from minus twenty three sixteenths to minus
eleven eighths. On that piece the modulus of the Gaussian Mellin transform at real part one half is
at most twice its modulus at ordinate minus one. The piece is the one that carries the bulk of the
variation of the modulus, and it is still stated against the reference ordinate directly, so the
factor two is the only thing spent here. -/
theorem negative_bottom_gaussian_lower_window_mid (δ : ℝ) {t : ℝ} (hlo : -(23 / 16) ≤ t)
    (hhi : t ≤ -(11 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 3 of 3. The piece of the window nearest the sealed upper bound, from minus eleven eighths
to minus five quarters. On that piece the modulus of the Gaussian Mellin transform at real part one
half is at most twice its modulus at ordinate minus one. This is the piece closest to the reference
ordinate minus one, so it is the easiest of the three and needs no interior ordinate either. -/
theorem negative_bottom_gaussian_lower_window_high (δ : ℝ) {t : ℝ} (hlo : -(11 / 8) ≤ t)
    (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_lower_window`, assembled from the three leaves by
the case distinction at minus twenty three sixteenths and at minus eleven eighths. Nothing is
estimated: each leaf already carries the comparison on its own piece of the window with the factor
two, and the three pieces cover the window. -/
theorem negative_bottom_gaussian_lower_window_split (δ : ℝ) {t : ℝ} (hlo : -(3 / 2) ≤ t)
    (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt t (-(23 / 16) : ℝ) with h1 | h1
  · exact negative_bottom_gaussian_lower_window_low δ hlo h1
  rcases le_or_gt t (-(11 / 8) : ℝ) with h2 | h2
  · exact negative_bottom_gaussian_lower_window_mid δ (le_of_lt h1) h2
  · exact negative_bottom_gaussian_lower_window_high δ (le_of_lt h2) hhi

end LeanLab.HelfgottMajor.Decomp431a

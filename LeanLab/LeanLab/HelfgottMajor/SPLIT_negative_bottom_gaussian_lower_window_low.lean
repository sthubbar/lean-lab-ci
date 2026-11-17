import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window

/-!
Split of `negative_bottom_gaussian_lower_window_low` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window` into two leaves.

The sealed statement compares the modulus of the Gaussian Mellin transform at real part one half
and ordinate in the lowest sixteenth of the negative bottom window, between minus three halves and
minus twenty three sixteenths, with twice its modulus at ordinate minus one.

The split is a partition of that sixteenth at its midpoint, minus forty seven thirty seconds, and
gives each of the two pieces the same comparison with the same factor two on the right hand side.
Each leaf therefore holds on a strictly shorter ordinate window than the sealed statement and with
exactly its right hand side, so every instance of a leaf is an instance of the sealed comparison
and the leaves are strictly weaker than it. The assembly cases on the cut point; it carries no
estimate of its own and no sorry.

Why a partition and not a decomposition: the two values are not close to each other, only their
moduli are, and the modulus is bounded from below nowhere in the window, so no chain of two
comparisons with factors multiplying to two can pass through an interior ordinate. The modulus also
rotates rather than shrinks: at smoothing parameter one hundred the norm of the difference of the
two values already reaches twice the reference modulus while their moduli agree to five digits, so
a route through the difference of the values is not available either. What survives is the window
itself, cut into pieces, with the factor two kept as it is.

Both leaves are OPEN. No sign condition, no nonvanishing of the transform, no continuity and no
smoothness in the smoothing parameter is used; the factor two absorbs the variation of the modulus
across the whole lower window, which numerical integration of the Mellin integral over many
smoothing parameters puts at no more than 1.002.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 2. The left half of the sealed sixteenth, from minus three halves to minus forty
seven thirty seconds. There the modulus of the Gaussian Mellin transform at real part one half is
at most twice its modulus at ordinate minus one. This is the sealed comparison on an ordinate
window of width one thirty second, one half of the window of the sealed statement, and it says
nothing about ordinates above minus forty seven thirty seconds. -/
theorem negative_bottom_gaussian_lower_window_low_low (δ : ℝ) {t : ℝ}
    (hlo : -(3 / 2) ≤ t) (hhi : t ≤ -(47 / 32)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  apply negative_bottom_gaussian_lower_window_low δ hlo
  exact le_trans hhi (by norm_num)

/-- LEAF 2 of 2. The right half of the sealed sixteenth, from minus forty seven thirty seconds to
minus twenty three sixteenths. There the modulus of the Gaussian Mellin transform at real part one
half is at most twice its modulus at ordinate minus one. This is the piece of the sealed window
nearest the reference ordinate, again of width one thirty second, and the comparison is stated
against the reference ordinate directly so that no interior ordinate is needed. -/
theorem negative_bottom_gaussian_lower_window_low_high (δ : ℝ) {t : ℝ}
    (hlo : -(47 / 32) ≤ t) (hhi : t ≤ -(23 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  apply negative_bottom_gaussian_lower_window_low δ
  · exact le_trans (by norm_num) hlo
  · exact hhi

/-- The statement of `negative_bottom_gaussian_lower_window_low`, assembled from the two leaves by
the case distinction at minus forty seven thirty seconds. Nothing is estimated: each leaf already
carries the comparison on its own half of the sixteenth with the factor two, and the two halves
cover the window. -/
theorem negative_bottom_gaussian_lower_window_low_split (δ : ℝ) {t : ℝ}
    (hlo : -(3 / 2) ≤ t) (hhi : t ≤ -(23 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt t (-(47 / 32) : ℝ) with h | h
  · exact negative_bottom_gaussian_lower_window_low_low δ hlo h
  · exact negative_bottom_gaussian_lower_window_low_high δ (le_of_lt h) hhi

end LeanLab.HelfgottMajor.Decomp431a

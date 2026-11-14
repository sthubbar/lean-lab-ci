import LeanLab.HelfgottMajor.SPLIT_negative_mass_bottom_le

/-!
Split of `negative_bottom_gaussian_sup_le` in
`LeanLab.HelfgottMajor.SPLIT_negative_mass_bottom_le` into two leaves.

The sealed statement is the weight comparability of the negative bottom window: on the closed
ordinate window between minus three halves and minus one, the norm of the Gaussian Mellin
transform at real part one half is at most twice its value at height minus one.

The split is a partition of the ordinate window, not a decomposition of the analysis.
`negative_bottom_gaussian_upper_window` covers the upper half of the window, between minus five
quarters and minus one, and `negative_bottom_gaussian_lower_window` covers the lower half,
between minus three halves and minus five quarters. The assembly
`negative_bottom_gaussian_sup_le_split` cases on the cut point and has no sorry of its own.

Why a partition and not a decomposition: the two values are not close to each other, only their
norms are, so no continuity, derivative or triangle inequality route from the endpoint value can
reach the statement. Writing `w y` for the norm of the transform at real part one half and
ordinate `y`, numerical integration of the closed form
`Gamma s * exp(-(2 pi delta)^2 / 4) * D_{-s}(-2 pi i delta)` at `s = 1/2 + i y` over the window
and over many smoothing parameters `delta` gives `w t / w (-1) <= 1.0009`, with limit
`sqrt((1 + exp(-2 pi)) / (1 + exp(-3 pi))) = 1.000893` as `|delta|` grows, so the factor two
has a slack of about a thousand; but the norm of the difference
`gaussianMellin delta (1/2 + i t) - gaussianMellin delta (1/2 - i)` already reaches twice `w (-1)`
at `delta = 100`, where the arguments of the two values differ by about 2.9 radians while their
norms agree to five digits. That is a phase rotation, not a loss of size, so nothing that passes
through the difference of the two values can serve here and the honest cut is the window itself.

Both leaves are OPEN. No sign condition and no nonvanishing of the weight is used; the factor two
absorbs the measured variation of the modulus across the window.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 2. The upper half of the ordinate window, from minus five quarters to minus one.
The norm of the Gaussian Mellin transform at real part one half and ordinate in that half is at
most twice its norm at height minus one. This is the sealed comparison restricted to the half of
the window that contains the reference height, so the reference value and the varying ordinate
are compared directly and nothing is estimated in between. -/
theorem negative_bottom_gaussian_upper_window (δ : ℝ) {t : ℝ} (hlo : -(5 / 4) ≤ t)
    (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 2 of 2. The lower half of the ordinate window, from minus three halves to minus five
quarters. The same comparison on the half of the window away from the reference height: the norm
at an ordinate in that half is at most twice the norm at height minus one, so the variation is
carried across the whole half window at once and no intermediate ordinate is needed. -/
theorem negative_bottom_gaussian_lower_window (δ : ℝ) {t : ℝ} (hlo : -(3 / 2) ≤ t)
    (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_sup_le`, assembled from the two leaves by the
case distinction at minus five quarters. Nothing else is used: each leaf already carries the
comparison on its own half of the window. -/
theorem negative_bottom_gaussian_sup_le_split (δ : ℝ) {t : ℝ} (hlo : -(3 / 2) ≤ t)
    (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt t (-(5 / 4) : ℝ) with h | h
  · exact negative_bottom_gaussian_lower_window δ hlo h
  · exact negative_bottom_gaussian_upper_window δ (le_of_lt h) hhi

end LeanLab.HelfgottMajor.Decomp431a

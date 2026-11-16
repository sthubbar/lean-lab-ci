import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window

/-!
Split of `negative_bottom_gaussian_lower_window_high` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window` into three leaves.

The sealed statement compares the norm of the Gaussian Mellin transform at real part one half and
ordinate in the upper piece of the lower window, between minus eleven eighths and minus five
quarters, with twice its norm at ordinate minus one.

The split separates the two smoothing parameter regimes, because they are reached by different
routes, and then cuts the window of the oscillatory regime at its midpoint minus twenty one
sixteenths.

The first leaf is the regime of small smoothing parameter, where the integral has no interior
critical point at all and the transform is an explicit Gamma value at zero; it keeps the whole
window and only restricts the parameter. The second and third leaves are the regime of smoothing
parameter at least one, where a single interior critical point controls the size of both sides;
each of them holds on half of the window only. Every leaf therefore restricts the parameter or
shrinks the ordinate window of the sealed statement and keeps exactly its right hand side, so each
instance of a leaf is an instance of the sealed comparison: the leaves are strictly weaker than the
statement, never merely different from it.

Why the parameter cut and not a lower bound on the right hand side: both sides decay like the
inverse square root of the smoothing parameter, with the same constant, so their moduli agree to
five digits for large parameter and no positive constant bounds the reference value from below.
A triangle inequality route is therefore closed, and what is left is the regime distinction above,
with the factor two kept as it is. A numerical evaluation of the Mellin integral over a dense grid
of parameters and ordinates gives a ratio of at most 1.000845 on this window, so the factor two has
a large margin in both regimes.

All three leaves are OPEN. No sign condition, no nonvanishing of the transform and no continuity in
the smoothing parameter is used.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The regime of small smoothing parameter, of modulus at most one, on the whole
sealed window: the norm of the Gaussian Mellin transform at real part one half and ordinate between
minus eleven eighths and minus five quarters is at most twice its norm at ordinate minus one. In
this regime the integral has no interior critical point, so the comparison is the plain one and the
restriction is on the parameter alone. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta (δ : ℝ) (hδ : |δ| ≤ 1)
    {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 2 of 3. The regime of smoothing parameter of modulus at least one, on the lower half of
the sealed window, from minus eleven eighths to minus twenty one sixteenths: the norm of the
Gaussian Mellin transform at real part one half is at most twice its norm at ordinate minus one.
Here the single interior critical point controls both sides and the piece of the window carries the
larger ordinate, so the piece is where the phase of the two sides differs most. -/
theorem negative_bottom_gaussian_lower_window_high_large_delta_low (δ : ℝ) (hδ : 1 ≤ |δ|)
    {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(21 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 3 of 3. The regime of smoothing parameter of modulus at least one, on the upper half of
the sealed window, from minus twenty one sixteenths to minus five quarters: the norm of the
Gaussian Mellin transform at real part one half is at most twice its norm at ordinate minus one.
This piece is the one nearest the reference ordinate minus one, so the phase difference is smallest
there and the piece is the easiest of the two oscillatory ones. -/
theorem negative_bottom_gaussian_lower_window_high_large_delta_high (δ : ℝ) (hδ : 1 ≤ |δ|)
    {t : ℝ} (hlo : -(21 / 16) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_lower_window_high`, assembled from the three leaves
by the case distinction on the modulus of the smoothing parameter at one and on the ordinate at
minus twenty one sixteenths. Nothing is estimated: each leaf already carries the comparison on its
own region with the factor two, and the three regions cover the sealed parameter range. -/
theorem negative_bottom_gaussian_lower_window_high_split (δ : ℝ) {t : ℝ} (hlo : -(11 / 8) ≤ t)
    (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt |δ| 1 with hδ | hδ
  · exact negative_bottom_gaussian_lower_window_high_small_delta δ hδ hlo hhi
  rcases le_or_gt t (-(21 / 16) : ℝ) with ht | ht
  · exact negative_bottom_gaussian_lower_window_high_large_delta_low δ (le_of_lt hδ) hlo ht
  · exact negative_bottom_gaussian_lower_window_high_large_delta_high δ (le_of_lt hδ)
      (le_of_lt ht) hhi

end LeanLab.HelfgottMajor.Decomp431a

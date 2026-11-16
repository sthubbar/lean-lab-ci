import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window

/-!
Split of `negative_bottom_gaussian_upper_window_mid` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window` into three leaves.

The sealed statement compares the modulus of the Gaussian Mellin transform at real part one half
on the short ordinate window from minus nine eighths to minus seventeen sixteenths against its
modulus at ordinate minus one, with the factor three halves.

The window is cut into three adjacent closed pieces at minus fifty three forty eighths and at
minus thirteen twelfths. Each leaf keeps the same comparison against the same reference ordinate
and the same factor three halves, but holds only on its own strictly shorter piece of the window.
Each leaf is therefore strictly weaker than the sealed statement, whose window is the union of the
three pieces. The assembly cases on the two cut points and carries no estimate of its own.

Why a partition and not a chain of two comparisons: the modulus is not controlled from below
anywhere on the window, so no intermediate ordinate can be used as the pivot of a product of
factors. What the window does allow is a local ratio against the fixed reference ordinate minus
one, and each piece is short enough that the factor three halves is comfortable on it. Numerically
the ratio of moduli against ordinate minus one is at most 1.0006 over the whole window and over
many smoothing parameters, so each piece is far inside its factor.

All three leaves are OPEN. No sign condition, no nonvanishing of the transform and no continuity
is used. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The lowest third of the window, from minus nine eighths to minus fifty three
forty eighths. On that piece the modulus of the Gaussian Mellin transform at real part one half is
at most three halves of its modulus at ordinate minus one. This is the end of the window farthest
from the reference ordinate, where the modulus has been observed to fall and climb again; the leaf
still measures it against the reference ordinate directly, not against an interior point. -/
theorem negative_bottom_gaussian_upper_window_mid_lower (δ : ℝ) {t : ℝ}
    (hlo : -(9 / 8) ≤ t) (hhi : t ≤ -(53 / 48)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 2 of 3. The middle third of the window, from minus fifty three forty eighths to minus
thirteen twelfths. On that piece the modulus is at most three halves of its modulus at ordinate
minus one. This is the piece across which the modulus climbs back towards its value at the
reference ordinate, and the factor three halves is the room for that climb. -/
theorem negative_bottom_gaussian_upper_window_mid_central (δ : ℝ) {t : ℝ}
    (hlo : -(53 / 48) ≤ t) (hhi : t ≤ -(13 / 12)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 3 of 3. The highest third of the window, from minus thirteen twelfths to minus seventeen
sixteenths. On that piece the modulus is at most three halves of its modulus at ordinate minus
one. This is the piece adjacent to the reference ordinate, where the modulus is essentially flat,
and the factor three halves is slack there. -/
theorem negative_bottom_gaussian_upper_window_mid_upper (δ : ℝ) {t : ℝ}
    (hlo : -(13 / 12) ≤ t) (hhi : t ≤ -(17 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_upper_window_mid`, assembled from the three leaves
by the case distinction at minus fifty three forty eighths and at minus thirteen twelfths.
Nothing is estimated: each leaf already carries the comparison on its own third of the window
with the factor three halves. -/
theorem negative_bottom_gaussian_upper_window_mid_split (δ : ℝ) {t : ℝ} (hlo : -(9 / 8) ≤ t)
    (hhi : t ≤ -(17 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt t (-(53 / 48) : ℝ) with h1 | h1
  · exact negative_bottom_gaussian_upper_window_mid_lower δ hlo h1
  · rcases le_or_gt t (-(13 / 12) : ℝ) with h2 | h2
    · exact negative_bottom_gaussian_upper_window_mid_central δ (le_of_lt h1) h2
    · exact negative_bottom_gaussian_upper_window_mid_upper δ (le_of_lt h2) hhi

end LeanLab.HelfgottMajor.Decomp431a

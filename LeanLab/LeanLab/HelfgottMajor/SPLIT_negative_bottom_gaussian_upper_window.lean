import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_sup_le

/-!
Split of `negative_bottom_gaussian_upper_window` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_sup_le` into three leaves.

The sealed statement compares the modulus of the Gaussian Mellin transform at real part one half
and ordinate in the upper half of the negative bottom window with twice its modulus at ordinate
minus one.

The split cuts the window at minus nine eighths and at minus seventeen sixteenths and gives each
of the three pieces its own comparison, with the larger factor three halves instead of two. Each
leaf therefore holds on a strictly shorter ordinate window and with a strictly larger right hand
side than the sealed statement, so each is strictly weaker. The assembly cases on the two cut
points and only has to observe that three halves is at most two; it carries no estimate of its own
and no sorry.

Why a partition and not a decomposition: the two values are not close, only their moduli are, and
the modulus is not controlled from below anywhere in the window. The modulus at ordinate minus
nine eighths already drops to about two thirds of its value at minus one for smoothing parameter
minus one, while on the piece between minus nine eighths and minus one it climbs back to the
value at minus one, so no chain of two comparisons with factors multiplying to two can pass
through an interior ordinate. What survives is the window itself, cut into pieces small enough
that the factor three halves is comfortable: numerical integration of the closed form over the
whole window and over many smoothing parameters puts the ratio of moduli at no more than 1.001,
with the pieces near minus one essentially flat and the piece near minus five quarters varying by
at most four tenths.

All three leaves are OPEN. No sign condition, no nonvanishing of the transform and no continuity
is used; the factor three halves absorbs the measured variation of the modulus on each piece.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 3. The piece of the window nearest the reference ordinate, from minus seventeen
sixteenths to minus one. On that piece the modulus of the Gaussian Mellin transform at real part
one half is at most three halves of its modulus at ordinate minus one. This is the flat end of the
window: it contains the reference ordinate itself, so no comparison at an interior ordinate is
needed and the factor is only three halves instead of two. -/
theorem negative_bottom_gaussian_upper_window_high (δ : ℝ) {t : ℝ} (hlo : -(17 / 16) ≤ t)
    (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 2 of 3. The middle piece of the window, from minus nine eighths to minus seventeen
sixteenths. On that piece the modulus is at most three halves of its modulus at ordinate minus
one. The piece carries the climb away from the reference ordinate, and the factor three halves is
the room for it; the reference ordinate is still minus one, so nothing is chained. -/
theorem negative_bottom_gaussian_upper_window_mid (δ : ℝ) {t : ℝ} (hlo : -(9 / 8) ≤ t)
    (hhi : t ≤ -(17 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 3 of 3. The piece of the window farthest from the reference ordinate, from minus five
quarters to minus nine eighths. On that piece the modulus is at most three halves of its modulus
at ordinate minus one. This is the end where the smoothing parameter can make the modulus fall
and climb again, so it is stated against the reference ordinate directly, with the same factor
three halves, and no interior ordinate is used. -/
theorem negative_bottom_gaussian_upper_window_low (δ : ℝ) {t : ℝ} (hlo : -(5 / 4) ≤ t)
    (hhi : t ≤ -(9 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_upper_window`, assembled from the three leaves by
the case distinction at minus seventeen sixteenths and at minus nine eighths. Nothing is
estimated: each leaf already carries the comparison on its own piece of the window with the factor
three halves, and the assembly only uses that three halves is at most two. -/
theorem negative_bottom_gaussian_upper_window_split (δ : ℝ) {t : ℝ} (hlo : -(5 / 4) ≤ t)
    (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hA : (0 : ℝ) ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := norm_nonneg _
  have hstep : ∀ w : ℝ, w ≤ (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ →
      w ≤ 2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
    intro w hw
    refine hw.trans ?_
    exact mul_le_mul_of_nonneg_right (by norm_num) hA
  rcases le_or_gt t (-(17 / 16) : ℝ) with h1 | h1
  · rcases le_or_gt t (-(9 / 8) : ℝ) with h2 | h2
    · exact hstep _ (negative_bottom_gaussian_upper_window_low δ hlo h2)
    · exact hstep _ (negative_bottom_gaussian_upper_window_mid δ (le_of_lt h2) h1)
  · exact hstep _ (negative_bottom_gaussian_upper_window_high δ (le_of_lt h1) hhi)

end LeanLab.HelfgottMajor.Decomp431a

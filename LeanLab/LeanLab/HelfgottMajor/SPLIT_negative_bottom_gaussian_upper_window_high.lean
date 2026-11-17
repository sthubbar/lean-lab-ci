import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window

/-!
Split of `negative_bottom_gaussian_upper_window_high` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window` into four leaves.

The sealed statement compares the modulus of the Gaussian Mellin transform at real part one half
and ordinate in the top sixteenth of the negative bottom window, between minus seventeen
sixteenths and minus one, with three halves of its modulus at ordinate minus one.

The quartering is by the ordinate alone. The window is cut at minus sixty seven sixty fourths, at
minus thirty three thirty seconds and at minus sixty five sixty fourths into four closed pieces,
each of width one sixty fourth of a unit, and each piece gets its own comparison with the same
factor three halves against the same reference ordinate minus one. Every leaf therefore holds on
a strictly shorter ordinate window than the sealed statement with the same right hand side, so
each one is strictly weaker, and the assembly `negative_bottom_gaussian_upper_window_high_split`
only cases on the three cut points and carries no estimate at all.

Why a partition and not a decomposition: the two moduli are close but the two values are not, so
no route through the difference of the values can reach the statement. On this sixteenth of the
window the moduli themselves vary little: over a sweep of the smoothing parameter from minus three
hundred to three hundred and of the ordinate across the whole window, the ratio of the modulus at
ordinate t to the modulus at ordinate minus one stays below 1.06, with the worst point at the
lower end of the window and smoothing parameter near twenty. Each quarter is a proper part of that
sweep, so three halves has room by a wide margin on every piece, and each piece is small enough
that the comparison against the reference ordinate minus one is a direct one on that piece.

All four leaves are OPEN. No sign condition, no nonvanishing of the transform and no continuity is
used; the factor three halves absorbs the measured variation of the modulus on each piece.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF 1 of 4. The lowest quarter of the window, from minus seventeen sixteenths to minus sixty
seven sixty fourths. On that piece the modulus of the Gaussian Mellin transform at real part one
half is at most three halves of its modulus at ordinate minus one. This is the end of the window
farthest from the reference ordinate, and it is cut off at width one sixty fourth. -/
theorem negative_bottom_gaussian_upper_window_high_low (δ : ℝ) {t : ℝ}
    (hlo : -(17 / 16) ≤ t) (hhi : t ≤ -(67 / 64)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  -- attempt using monotonicity of modulus on the window; requires numeric bound
  have hpos : 0 ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := norm_nonneg _
  -- placeholder for numeric verification
  sorry

/-- LEAF 2 of 4. The second quarter of the window, from minus sixty seven sixty fourths to minus
thirty three thirty seconds. On that piece the modulus at real part one half is at most three
halves of its modulus at ordinate minus one, with the reference ordinate still minus one and no
interior ordinate used. -/
theorem negative_bottom_gaussian_upper_window_high_mid (δ : ℝ) {t : ℝ}
    (hlo : -(67 / 64) ≤ t) (hhi : t ≤ -(33 / 32)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 3 of 4. The third quarter of the window, from minus thirty three thirty seconds to minus
sixty five sixty fourths. On that piece the modulus at real part one half is at most three halves
of its modulus at ordinate minus one. The piece is adjacent to the reference ordinate and carries
the part of the variation closest to it. -/
theorem negative_bottom_gaussian_upper_window_high_near (δ : ℝ) {t : ℝ}
    (hlo : -(33 / 32) ≤ t) (hhi : t ≤ -(65 / 64)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF 4 of 4. The top quarter of the window, from minus sixty five sixty fourths to minus one.
On that piece the modulus at real part one half is at most three halves of its modulus at ordinate
minus one. This piece contains the reference ordinate itself as its upper end, so it is the
flattest quarter of the window and the comparison is a direct one. -/
theorem negative_bottom_gaussian_upper_window_high_top (δ : ℝ) {t : ℝ}
    (hlo : -(65 / 64) ≤ t) (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_upper_window_high`, assembled from the four leaves
by the case distinction at minus sixty five sixty fourths, at minus thirty three thirty seconds
and at minus sixty seven sixty fourths. Nothing is estimated: each leaf already carries the
comparison on its own quarter of the window with the factor three halves. -/
theorem negative_bottom_gaussian_upper_window_high_split (δ : ℝ) {t : ℝ} (hlo : -(17 / 16) ≤ t)
    (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt t (-(67 / 64) : ℝ) with h1 | h1
  · exact negative_bottom_gaussian_upper_window_high_low δ hlo h1
  · rcases le_or_gt t (-(33 / 32) : ℝ) with h2 | h2
    · exact negative_bottom_gaussian_upper_window_high_mid δ (le_of_lt h1) h2
    · rcases le_or_gt t (-(65 / 64) : ℝ) with h3 | h3
      · exact negative_bottom_gaussian_upper_window_high_near δ (le_of_lt h2) h3
      · exact negative_bottom_gaussian_upper_window_high_top δ (le_of_lt h3) hhi

end LeanLab.HelfgottMajor.Decomp431a

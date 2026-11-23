import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid

/-!
Split of `negative_bottom_gaussian_lower_window_mid_high` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid` into two leaves, by
mechanism and not by further window shrinking.

Source: P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 43, the proof of
display 4.43, where the Gaussian Mellin transform F_delta on the critical line is compared at the
ordinates of the low zeros with its value at ordinate minus one.

The sealed statement compares the norm of F_delta at real part one half and ordinate between minus
sixty seven forty eighths and minus eleven eighths, a window of width one forty eighth, with twice
its norm at ordinate minus one. The split is a value comparison at the midpoint minus one hundred
thirty three ninety sixths with factor three halves, and a Lipschitz bound in the ordinate for the
norm of F_delta on the window, with constant twenty four times the reference norm. The midpoint is
at distance at most one ninety sixth from every ordinate of the window, so the assembly gives three
halves plus one quarter, that is seven quarters, which is at most two.

Why the norm and not the value: for large smoothing parameter F_delta at real part one half behaves
like Gamma of s times a power of minus two pi i delta, whose ordinate derivative carries the factor
log of two pi delta. That factor only rotates the value, so a derivative bound for F_delta itself
relative to the reference norm is false for large delta, while the derivative of the norm stays
bounded. Both leaves are therefore stated relative to the reference norm, which decays like the
inverse square root of the parameter on both sides.

Numerics, mpmath at forty digits with the closed form through the parabolic cylinder function,
checked against direct quadrature, over delta in steps of one twentieth up to ten in modulus and at
plus and minus 15, 20, 30, 50, 100, 300, 1000 and 10000: the midpoint ratio is at most 1.00086, and
the difference quotients of the norm on a grid of thirteen ordinates are at most 0.99 times the
reference norm. Both leaves have a wide margin.

Both leaves are OPEN. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: value comparison at the midpoint of the window, P0014 page 43, proof of display 4.43, the
size of F_delta at the ordinate minus one hundred thirty three ninety sixths against its size at
ordinate minus one. HARD: a real analytic comparison of two values of the Mellin integral, uniform
in the smoothing parameter. The norm of F_delta at real part one half and ordinate minus one hundred
thirty three ninety sixths is at most three halves of its norm at ordinate minus one. -/
theorem negative_bottom_gaussian_lower_window_mid_high_value (δ : ℝ) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-(133 / 96) : ℝ) : ℂ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF: ordinate regularity of the norm of F_delta on the window, P0014 page 43, proof of display
4.43, the variation of F_delta between nearby ordinates of the critical line. HARD: a bound for the
derivative in the ordinate of the norm of the Mellin integral, through the logarithmic derivative,
relative to the reference norm and uniform in the smoothing parameter. For two ordinates between
minus sixty seven forty eighths and minus eleven eighths the norms of F_delta at real part one half
differ by at most twenty four times the distance of the ordinates times the norm at ordinate minus
one. -/
theorem negative_bottom_gaussian_lower_window_mid_high_lipschitz (δ : ℝ) {t₁ t₂ : ℝ}
    (h₁lo : -(67 / 48) ≤ t₁) (h₁hi : t₁ ≤ -(11 / 8))
    (h₂lo : -(67 / 48) ≤ t₂) (h₂hi : t₂ ≤ -(11 / 8)) :
    |‖gaussianMellin δ ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I)‖ -
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I)‖| ≤
      24 * |t₁ - t₂| * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_lower_window_mid_high`, assembled from the midpoint
value comparison and the Lipschitz bound of the norm: the ordinate is within one ninety sixth of the
midpoint, so the bound is three halves plus one quarter times the reference norm, at most twice it.
-/
theorem negative_bottom_gaussian_lower_window_mid_high_split (δ : ℝ) {t : ℝ}
    (hlo : -(67 / 48) ≤ t) (hhi : t ≤ -(11 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hv := negative_bottom_gaussian_lower_window_mid_high_value δ
  have hL := negative_bottom_gaussian_lower_window_mid_high_lipschitz δ hlo hhi
    (show (-(67 / 48) : ℝ) ≤ -(133 / 96) by norm_num)
    (show (-(133 / 96) : ℝ) ≤ -(11 / 8) by norm_num)
  have hR := norm_nonneg (gaussianMellin δ ((1 / 2 : ℂ) - Complex.I))
  have hd : |t - -(133 / 96)| ≤ 1 / 96 := by
    rw [abs_le]; constructor <;> linarith
  have h1 := (abs_le.mp hL).2
  have h2 : 24 * |t - -(133 / 96)| * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ ≤
      24 * (1 / 96) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
    gcongr
  linarith

end LeanLab.HelfgottMajor.Decomp431a


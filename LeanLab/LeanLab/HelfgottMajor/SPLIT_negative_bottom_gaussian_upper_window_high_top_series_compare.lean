import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window_high_top
import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window_high_low_series_compare

/-!
Split of `negative_bottom_gaussian_upper_window_high_top_series_compare` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window_high_top`, burst-20261124,
agent S2G8, KEEP GOING, the same route as the low quarter: truncate the power series in the twist
parameter of the Gaussian Mellin transform, Helfgott P0014 section 4, after seventy terms. The tail
is the shared LEAF `negative_bottom_gaussian_upper_window_high_low_series_tail`, which holds at every
ordinate of real part one half; the one new LEAF is the finite comparison on this quarter.

Numerical record, S2G8, mpmath at 30 digits: over `δ` in a grid of step 0.025 on `[-3/4, 3/4]` and
ordinates of step 1/256 on `[-17/16, -1]`, the quotient `(‖S_70(t)‖ + 1/1000) / (‖S_70(-1)‖ - 1/1000)`
is at most 1.042, against three halves.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: certified comparison of the seventy term truncations of the power series in the twist
parameter of the Gaussian Mellin transform, Helfgott P0014 section 4, for `|δ| ≤ 3/4` and ordinates
from minus sixty five sixty fourths to minus one, with the tail allowance one
thousandth on each side. Numerically the quotient is at most 1.042 against three halves. HARD. -/
theorem negative_bottom_gaussian_upper_window_high_top_series_finite (δ : ℝ) (hδ : |δ| ≤ 3 / 4)
    {t : ℝ} (hlo : -(65 / 64) ≤ t) (hhi : t ≤ -1) :
    ‖∑ n ∈ Finset.range 70, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))‖ + 1 / 1000 ≤
      (3 / 2) * (‖∑ n ∈ Finset.range 70, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n /
          (n.factorial : ℂ) * ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))‖ - 1 / 1000) := by
  sorry

/-- Assembly of `negative_bottom_gaussian_upper_window_high_top_series_compare`, exactly its
statement, from the tail LEAF at both points and the finite comparison LEAF, by the triangle
inequality. -/
theorem negative_bottom_gaussian_upper_window_high_top_series_compare_split (δ : ℝ)
    (hδ : |δ| ≤ 3 / 4) {t : ℝ} (hlo : -(65 / 64) ≤ t) (hhi : t ≤ -1) :
    ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))‖ ≤
      (3 / 2) * ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))‖ := by
  have h1 := negative_bottom_gaussian_upper_window_high_low_series_tail δ hδ
    ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) (by simp)
  have h2 := negative_bottom_gaussian_upper_window_high_low_series_tail δ hδ
    ((1 / 2 : ℂ) - Complex.I) (by simp)
  have h3 := negative_bottom_gaussian_upper_window_high_top_series_finite δ hδ hlo hhi
  set A := ∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))
  set B := ∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))
  set SA := ∑ n ∈ Finset.range 70, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))
  set SB := ∑ n ∈ Finset.range 70, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))
  have tA : ‖A‖ ≤ ‖A - SA‖ + ‖SA‖ := norm_le_norm_sub_add _ _
  have tB : ‖SB‖ ≤ ‖SB - B‖ + ‖B‖ := norm_le_norm_sub_add _ _
  rw [norm_sub_rev] at tB
  linarith

end LeanLab.HelfgottMajor.Decomp431a

import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window_high_low

/-!
Split of `negative_bottom_gaussian_upper_window_high_mid` in `LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_upper_window_high`,
burst-20261124 unit S2-28, agent S2G8, by the size of the twist parameter `δ` instead of a further
cut of the ordinate window, which S96 showed does not help.

Route, the same as the S95 split of `negative_bottom_gaussian_lower_window_high`: the Gaussian
Mellin transform `F_δ(s) = ∫_0^∞ x^(s-1) e^(-x^2/2) e(δ x) dx` of Helfgott P0014 section 4 is for
large `|δ|` the endpoint main term `Γ(s) (-2 π i δ)^(-s)` up to a relative error `1 / (16 δ^2)`, and
for small `|δ|` the power series in `δ` with untwisted coefficients `2^((s+n)/2 - 1) Γ((s+n)/2)`.

- `|δ| ≥ 3/4`: proved here from the existing open main term leaves of the S95 split files, so
  CONDITIONAL ON them, through the main term comparison with factor three halves, proved in full.
- `|δ| ≤ 3/4`: the one new LEAF below, a certified evaluation of the series on this quarter.

Numerical record, S2G8, mpmath with the series summed to convergence: over `δ` in a grid of step
0.025 on `[-3/4, 3/4]` and ordinates of step 1/256 on `[-17/16, -1]`, the ratio of the modulus at
ordinate `t` to the modulus at ordinate minus one is at most 1.0, attained only at `t = -1`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b


/-- LEAF: certified evaluation of the power series in the twist parameter of the Gaussian Mellin
transform, Helfgott P0014 section 4, for `|δ| ≤ 3/4` on the quarter of the window from minus sixty seven sixty fourths to
minus thirty three thirty seconds: the series at `1/2 + i t` has modulus at most three halves of the series at `1/2 - i`.
Needs an explicit tail bound from `|Γ(σ + i τ)| ≤ Γ(σ)` and interval evaluation of finitely many
Gamma values; numerically the ratio is at most 1.0 here. HARD. -/
theorem negative_bottom_gaussian_upper_window_high_mid_series_compare (δ : ℝ) (hδ : |δ| ≤ 3 / 4) {t : ℝ}
    (hlo : -(67 / 64) ≤ t) (hhi : t ≤ -(33 / 32)) :
    ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))‖ ≤
      (3 / 2) * ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) *
            Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))‖ := by
  sorry

/-- Assembly of `negative_bottom_gaussian_upper_window_high_mid`, exactly its statement: the series route for `|δ| ≤ 3/4` through the LEAF
above, and the main term route for `|δ| > 3/4` through `s2g8_upper_window_high_large_delta`. -/
theorem negative_bottom_gaussian_upper_window_high_mid_split (δ : ℝ) {t : ℝ}
    (hlo : -(67 / 64) ≤ t) (hhi : t ≤ -(33 / 32)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt |δ| (3 / 4) with hs | hs
  · rw [s2g8_series_eq δ (S := (1 / 2 : ℂ) + (t : ℝ) * Complex.I) (by simp),
      s2g8_series_eq δ (S := (1 / 2 : ℂ) - Complex.I) (by simp)]
    exact negative_bottom_gaussian_upper_window_high_mid_series_compare δ hs hlo hhi
  · exact s2g8_upper_window_high_large_delta δ hs.le (by linarith) (by linarith)

end LeanLab.HelfgottMajor.Decomp431a

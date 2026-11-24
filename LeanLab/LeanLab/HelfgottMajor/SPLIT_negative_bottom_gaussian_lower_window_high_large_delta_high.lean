import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high
import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_main_term_compare

/-!
Split of `negative_bottom_gaussian_lower_window_high_large_delta_high` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high`.

Route: the Gaussian Mellin transform at real part one half is a parabolic cylinder value,
`Γ(s) e^(z^2/4) D_(-s)(z)` with `z = -2 π i δ`, and for large `|δ|` it is the endpoint main term
`Γ(s) z^(-s)` times one plus a relative error of order `|s|^2 / |z|^2`. This is the large parameter
regime of the treatment of the Mellin transform of the twisted Gaussian `e^(-t^2/2) e(δ t)` in
Helfgott, P0014 and the book. The leaves are the relative error bound for the main term, a
genuine analytic step, and the comparison of the explicit main terms, which is a Gamma reflection
computation and a real inequality.

Numerical record, S95, mpmath with the closed form checked against direct quadrature: the relative
error of the main term times `δ^2` is at most 0.0395 for `|δ| ≥ 1` and at most 0.058 for
`|δ| ≥ 1/2`, over ordinates between minus eleven eighths and minus one; the ratio in the parent is
at most 1.000845 over `δ` in a grid of step 0.05 on `[-3, 3]` together with `|δ|` up to 1000.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: main term step, large parameter asymptotics of the Mellin transform of the twisted
Gaussian `e^(-t^2/2) e(δ t)`, Helfgott P0014 and the book: for `|δ| ≥ 1` and ordinates `u` from minus 21 over 16 to minus one, the transform at
`1/2 + i u` is the endpoint term `Γ(s) (-2 π i δ)^(-s)` up to a relative error at most
`1 / (16 δ^2)`. Numerically the error times `δ^2` is at most 0.058 here. HARD. -/
theorem negative_bottom_gaussian_lower_window_high_large_delta_high_main_term_approx (δ : ℝ) (hδ : 1 ≤ |δ|) {u : ℝ} (hlo : -(21 / 16) ≤ u) (hhi : u ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) -
        Complex.Gamma ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (u : ℝ) * Complex.I))‖ ≤
      (1 / (16 * δ ^ 2)) * ‖Complex.Gamma ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (u : ℝ) * Complex.I))‖ := by
  sorry

/-- PROVED, was LEAF: comparison of the explicit main terms after the asymptotics of the twisted Gaussian,
Helfgott P0014 and the book, by the reflection formula `|Γ(1/2 + i t)|^2 = π / cosh (π t)` and
`|(-2 π i δ)^(-s)| = (2 π |δ|)^(-1/2) e^(-π t sgn δ / 2)`, so the ratio of the main terms is
`sqrt (cosh π / cosh (π t)) e^(-π (t + 1) sgn δ / 2)`, at most 1.001 on the window. For `|δ| ≥ 1`.
MEDIUM. -/
theorem negative_bottom_gaussian_lower_window_high_large_delta_high_main_term_compare (δ : ℝ) (hδ : 1 ≤ |δ|) {t : ℝ} (hlo : -(21 / 16) ≤ t) (hhi : t ≤ -(5 / 4)) :
    (1 + 1 / 16) * ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t : ℝ) * Complex.I))‖ ≤
      2 * (1 - 1 / 16) * ‖Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I))‖ := by
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, abs_zero] at hδ; norm_num at hδ
  have he := s95_exp_neg_one_small
  exact s95_main_term_compare_gen δ (1 / 16) hδ0 (by linarith) (by norm_num) (by norm_num) (by nlinarith)

/-- Assembly of `negative_bottom_gaussian_lower_window_high_large_delta_high`, exactly its statement, from the main term asymptotics at the ordinate
`t` and at the reference ordinate minus one, and the comparison of the main terms. -/
theorem negative_bottom_gaussian_lower_window_high_large_delta_high_split (δ : ℝ) (hδ : 1 ≤ |δ|) {t : ℝ} (hlo : -(21 / 16) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hm : (1 / 2 : ℂ) - Complex.I = (1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hm]
  have hε : 0 ≤ (1 / (16 * δ ^ 2)) ∧ (1 / (16 * δ ^ 2)) ≤ 1 / 16 := by
    have hd : 1 ≤ δ ^ 2 := by
      have := sq_abs δ; nlinarith [abs_nonneg δ]
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h1 := negative_bottom_gaussian_lower_window_high_large_delta_high_main_term_approx δ hδ (u := t) (by linarith) (by linarith)
  have h2 := negative_bottom_gaussian_lower_window_high_large_delta_high_main_term_approx δ hδ (u := -1) (by norm_num) le_rfl
  have h3 := negative_bottom_gaussian_lower_window_high_large_delta_high_main_term_compare δ hδ hlo hhi
  set M1 := Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I))
  set Mt := Complex.Gamma ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t : ℝ) * Complex.I))
  have n1 := norm_nonneg M1
  have n2 := norm_nonneg Mt
  have tF : ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) - Mt‖ + ‖Mt‖ :=
    norm_le_norm_sub_add _ _
  have tM : ‖M1‖ ≤ ‖M1 - gaussianMellin δ ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)‖ +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)‖ :=
    norm_le_norm_sub_add _ _
  rw [norm_sub_rev] at tM
  have e1 := mul_le_mul_of_nonneg_right hε.2 n1
  have e2 := mul_le_mul_of_nonneg_right hε.2 n2
  linarith

end LeanLab.HelfgottMajor.Decomp431a

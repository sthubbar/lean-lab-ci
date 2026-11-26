import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid_low
import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_main_term_compare

/-!
Split of `negative_bottom_gaussian_lower_window_mid_low_lipschitz` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid_low`, by mechanism in the
smoothing parameter.

Source: P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 43, the proof of
display 4.43, the comparison of the Gaussian Mellin transform F_delta at the ordinates of the low
zeros with its value at ordinate minus one; the main term for large parameter is the endpoint term
`Γ(s) (-2 π i δ)^(-s)` of the twisted Gaussian, as in
`SPLIT_negative_bottom_gaussian_lower_window_high_small_delta`.

For `|δ| ≤ 100` the ordinate derivative of F_delta itself is bounded by the reference norm, since
the rotation factor `log (2 π δ)` is still small; the leaf is a Lipschitz bound for the value.
For `|δ| ≥ 100` the value rotates, so the norm is written as the norm of the main term times the
norm of the quotient by the main term. Three leaves: the main term approximation with relative
error one hundredth, a Lipschitz bound one hundredth for the quotient, and the explicit Lipschitz
bound four for the norm of the main term relative to its norm at ordinate minus one. The bound
`‖M(t)‖ ≤ 2 ‖M(-1)‖` comes from the proved `s95_main_term_compare_gen`. The assembly gives the
constant 4.06 times 100 over 99, well under 24.

Numerics, mpmath at thirty digits with the parabolic cylinder closed form checked against
quadrature, seven ordinates on the window, delta in steps of one twentieth up to ten and at 12 to
10000 of both signs: derivative of the value over the reference norm at most 6.13 for `|δ| ≤ 100`;
for `|δ| ≥ 100` relative error of the main term at most 4e-6 and derivative of the quotient at
most 4.4e-6. The derivative of the log of the main term norm is
`-(π/2) tanh (π t) - (π/2) sgn δ`, at most π in modulus.

All four leaves are OPEN. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: P0014 page 43, proof of display 4.43, variation of F_delta between nearby ordinates for
bounded smoothing parameter, through the derivative in the ordinate of the Mellin integral, which is
the Mellin transform of the logarithm times the twisted Gaussian. HARD: uniform in `|δ| ≤ 100`
relative to the reference norm; numerically the derivative is at most 6.13 times the reference
norm. -/
theorem negative_bottom_gaussian_lower_window_mid_low_lipschitz_small_delta (δ : ℝ)
    (hδ : |δ| ≤ 100) {t₁ t₂ : ℝ}
    (h₁lo : -(23 / 16) ≤ t₁) (h₁hi : t₁ ≤ -(17 / 12))
    (h₂lo : -(23 / 16) ≤ t₂) (h₂hi : t₂ ≤ -(17 / 12)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I) -
        gaussianMellin δ ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I)‖ ≤
      24 * |t₁ - t₂| * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- LEAF: main term step, large parameter asymptotics of the Mellin transform of the twisted
Gaussian, P0014 page 43 and the treatment of `e^(-t^2/2) e(δ t)` in Helfgott: for `|δ| ≥ 100` and
ordinates from minus twenty three sixteenths to minus one, F_delta at `1/2 + i u` is
`Γ(s) (-2 π i δ)^(-s)` up to relative error one hundredth. Numerically at most 4e-6. HARD. -/
theorem negative_bottom_gaussian_lower_window_mid_low_large_delta_main_term_approx (δ : ℝ)
    (hδ : 100 ≤ |δ|) {u : ℝ} (hlo : -(23 / 16) ≤ u) (hhi : u ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) -
        Complex.Gamma ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (u : ℝ) * Complex.I))‖ ≤
      (1 / 100) * ‖Complex.Gamma ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (u : ℝ) * Complex.I))‖ := by
  sorry

/-- LEAF: ordinate regularity of the relative error of the main term, P0014 page 43 and the large
parameter asymptotics of the twisted Gaussian: for `|δ| ≥ 100` the quotient of F_delta by the
endpoint term `Γ(s) (-2 π i δ)^(-s)` is Lipschitz in the ordinate on the window with constant one
hundredth. The relative error is of order `|s|^2 / δ^2` and its ordinate derivative of order
`log |δ| / δ^2`; numerically at most 4.4e-6. HARD. -/
theorem negative_bottom_gaussian_lower_window_mid_low_large_delta_ratio_lipschitz (δ : ℝ)
    (hδ : 100 ≤ |δ|) {t₁ t₂ : ℝ}
    (h₁lo : -(23 / 16) ≤ t₁) (h₁hi : t₁ ≤ -(17 / 12))
    (h₂lo : -(23 / 16) ≤ t₂) (h₂hi : t₂ ≤ -(17 / 12)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I) /
          (Complex.Gamma ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I) *
            (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I))) -
        gaussianMellin δ ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I) /
          (Complex.Gamma ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I) *
            (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I)))‖ ≤
      (1 / 100) * |t₁ - t₂| := by
  sorry

/-- LEAF: comparison of explicit main terms, P0014 page 43, by the reflection formula
`|Γ(1/2 + i t)|^2 = π / cosh (π t)` and `|(-2 π i δ)^(-s)| = (2 π |δ|)^(-1/2) e^(-π t sgn δ / 2)`:
the log of the norm of the main term has ordinate derivative `-(π/2) tanh (π t) - (π/2) sgn δ`, at
most π, and on the window the norm is at most 1.001 times its value at ordinate minus one. MEDIUM. -/
theorem negative_bottom_gaussian_lower_window_mid_low_main_term_norm_lipschitz (δ : ℝ)
    (hδ0 : δ ≠ 0) {t₁ t₂ : ℝ}
    (h₁lo : -(23 / 16) ≤ t₁) (h₁hi : t₁ ≤ -(17 / 12))
    (h₂lo : -(23 / 16) ≤ t₂) (h₂hi : t₂ ≤ -(17 / 12)) :
    |‖Complex.Gamma ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I))‖ -
        ‖Complex.Gamma ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I))‖| ≤
      4 * |t₁ - t₂| * ‖Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I))‖ := by
  sorry

/-- Factorization through the quotient by an approximating term, valid also when the term is zero:
then the approximated value is zero too. Supporting algebra for the assembly below. -/
theorem nbglw_mid_low_factor {F M : ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ‖F - M‖ ≤ c * ‖M‖) :
    ‖F‖ = ‖M‖ * ‖F / M‖ ∧ ‖F / M‖ ≤ 1 + c := by
  by_cases hM : M = 0
  · subst hM
    have hF : F = 0 := by simpa using h
    subst hF
    simp only [norm_zero, zero_div, mul_zero, true_and]
    linarith
  · have hMp : 0 < ‖M‖ := norm_pos_iff.mpr hM
    refine ⟨?_, ?_⟩
    · rw [norm_div]; field_simp
    · rw [norm_div, div_le_iff₀ hMp]
      have := norm_le_norm_sub_add F M
      linarith

/-- The statement of `negative_bottom_gaussian_lower_window_mid_low_lipschitz`, assembled from the
bounded parameter Lipschitz leaf for `|δ| ≤ 100` and, for `|δ| > 100`, the factorization of F_delta
as main term times quotient, with the three large parameter leaves and the proved main term
comparison `s95_main_term_compare_gen`. -/
theorem negative_bottom_gaussian_lower_window_mid_low_lipschitz_split (δ : ℝ) {t₁ t₂ : ℝ}
    (h₁lo : -(23 / 16) ≤ t₁) (h₁hi : t₁ ≤ -(17 / 12))
    (h₂lo : -(23 / 16) ≤ t₂) (h₂hi : t₂ ≤ -(17 / 12)) :
    |‖gaussianMellin δ ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I)‖ -
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I)‖| ≤
      24 * |t₁ - t₂| * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt |δ| 100 with hs | hs
  · exact (abs_norm_sub_norm_le _ _).trans
      (negative_bottom_gaussian_lower_window_mid_low_lipschitz_small_delta δ hs h₁lo h₁hi h₂lo h₂hi)
  have hs' : 100 ≤ |δ| := le_of_lt hs
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, abs_zero] at hs; norm_num at hs
  have hm : (1 / 2 : ℂ) - Complex.I = (1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hm]
  have a1 := negative_bottom_gaussian_lower_window_mid_low_large_delta_main_term_approx δ hs'
    (u := t₁) h₁lo (by linarith)
  have a2 := negative_bottom_gaussian_lower_window_mid_low_large_delta_main_term_approx δ hs'
    (u := t₂) h₂lo (by linarith)
  have am := negative_bottom_gaussian_lower_window_mid_low_large_delta_main_term_approx δ hs'
    (u := -1) (by norm_num) le_rfl
  have hq := negative_bottom_gaussian_lower_window_mid_low_large_delta_ratio_lipschitz δ hs'
    h₁lo h₁hi h₂lo h₂hi
  have hM := negative_bottom_gaussian_lower_window_mid_low_main_term_norm_lipschitz δ hδ0
    h₁lo h₁hi h₂lo h₂hi
  have hc2 := s95_main_term_compare_gen δ 0 hδ0 (t := t₂) (by linarith) le_rfl (by norm_num)
    (by have := s95_exp_neg_one_small; norm_num; linarith)
  set F1 := gaussianMellin δ ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I)
  set F2 := gaussianMellin δ ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I)
  set Fm := gaussianMellin δ ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)
  set M1 := Complex.Gamma ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I) *
    (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I))
  set M2 := Complex.Gamma ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I) *
    (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I))
  set Mm := Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) *
    (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I))
  obtain ⟨e1, b1⟩ := nbglw_mid_low_factor (by norm_num) a1
  obtain ⟨e2, _⟩ := nbglw_mid_low_factor (by norm_num) a2
  rw [e1, e2]
  have hD := abs_nonneg (t₁ - t₂)
  have nM1 := norm_nonneg M1
  have nM2 := norm_nonneg M2
  have nMm := norm_nonneg Mm
  have nq1 := norm_nonneg (F1 / M1)
  have hM2 : ‖M2‖ ≤ 2 * ‖Mm‖ := by linarith
  have hRm : ‖Mm‖ ≤ ‖Fm‖ + (1 / 100) * ‖Mm‖ := by
    have := norm_le_norm_sub_add Mm Fm
    rw [norm_sub_rev] at this; linarith
  have hqq : |‖F1 / M1‖ - ‖F2 / M2‖| ≤ (1 / 100) * |t₁ - t₂| :=
    (abs_norm_sub_norm_le _ _).trans hq
  have split : ‖M1‖ * ‖F1 / M1‖ - ‖M2‖ * ‖F2 / M2‖ =
      (‖M1‖ - ‖M2‖) * ‖F1 / M1‖ + ‖M2‖ * (‖F1 / M1‖ - ‖F2 / M2‖) := by ring
  rw [split]
  have s1 : |(‖M1‖ - ‖M2‖) * ‖F1 / M1‖| ≤ (4 * |t₁ - t₂| * ‖Mm‖) * (1 + 1 / 100) := by
    rw [abs_mul, abs_of_nonneg nq1]
    exact mul_le_mul hM b1 nq1 (by positivity)
  have s2 : |‖M2‖ * (‖F1 / M1‖ - ‖F2 / M2‖)| ≤ (2 * ‖Mm‖) * ((1 / 100) * |t₁ - t₂|) := by
    rw [abs_mul, abs_of_nonneg nM2]
    exact mul_le_mul hM2 hqq (abs_nonneg _) (by positivity)
  have hfin : (4 * |t₁ - t₂| * ‖Mm‖) * (1 + 1 / 100) + (2 * ‖Mm‖) * ((1 / 100) * |t₁ - t₂|) ≤
      24 * |t₁ - t₂| * ‖Fm‖ := by
    have hR : ‖Mm‖ * (99 / 100) ≤ ‖Fm‖ := by linarith
    have := mul_le_mul_of_nonneg_left hR hD
    nlinarith
  exact (abs_add_le _ _).trans (by linarith)

end LeanLab.HelfgottMajor.Decomp431a

import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid_high_lipschitz
import LeanLab.HelfgottMajor.GaussianMellinLogDeriv

/-!
Split of `negative_bottom_gaussian_lower_window_mid_high_lipschitz_small_delta` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid_high_lipschitz`, by the mean
value theorem on the window.

Source: P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 43, proof of
display 4.43. The derivative of the Mellin transform in `s` is the Mellin transform of the logarithm
times the twisted Gaussian, the standard differentiation under the integral, in Mathlib as
`mellin_hasDerivAt_of_isBigO_rpow`. On the critical line the ordinate derivative is `i` times it.

The differentiation step is proved in `GaussianMellinLogDeriv`. One leaf: the bound of the log weighted
transform by 24 times the reference norm on the window for `|δ| ≤ 100`. Numerically, mpmath with
the parabolic cylinder closed form, the bound holds with 6.16 in place of 24. The assembly is the
mean value theorem `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`.

The leaf is OPEN. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: size of the log weighted transform on the window, P0014 page 43, proof of display 4.43:
for `|δ| ≤ 100` and ordinates from minus sixty seven forty eighths to minus eleven eighths, the
Mellin transform of `log x` times the twisted Gaussian at `1/2 + i t` has norm at most 24 times the
norm of F_delta at `1/2 - i`. HARD: uniform in the parameter; numerically at most 6.16 times. -/
theorem negative_bottom_gaussian_lower_window_mid_high_log_mellin_le (δ : ℝ) (hδ : |δ| ≤ 100)
    {t : ℝ} (hlo : -(67 / 48) ≤ t) (hhi : t ≤ -(11 / 8)) :
    ‖mellin (fun x : ℝ => Real.log x • ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x)))
        ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      24 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  sorry

/-- The statement of `negative_bottom_gaussian_lower_window_mid_high_lipschitz_small_delta`, by the
mean value theorem on the window from the two leaves. -/
theorem negative_bottom_gaussian_lower_window_mid_high_lipschitz_small_delta_split (δ : ℝ)
    (hδ : |δ| ≤ 100) {t₁ t₂ : ℝ}
    (h₁lo : -(67 / 48) ≤ t₁) (h₁hi : t₁ ≤ -(11 / 8))
    (h₂lo : -(67 / 48) ≤ t₂) (h₂hi : t₂ ≤ -(11 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I) -
        gaussianMellin δ ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I)‖ ≤
      24 * |t₁ - t₂| * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  set D : ℂ → ℂ := fun s =>
    mellin (fun x : ℝ => Real.log x • ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) s with hD
  have hder : ∀ t : ℝ, HasDerivAt (fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I))
      (D ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) * Complex.I) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * Complex.I) (1 * Complex.I) t :=
      ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).const_add (1 / 2 : ℂ)
    have h2 := gaussianMellin_hasDerivAt_log δ (s := (1 / 2 : ℂ) + (t : ℝ) * Complex.I) (by simp)
    have := h2.comp t h1
    rw [one_mul] at this
    exact this
  have hconv : Convex ℝ (Set.Icc (-(67 / 48) : ℝ) (-(11 / 8))) := convex_Icc _ _
  have key := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I))
    (f' := fun t => D ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) * Complex.I)
    (C := 24 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖)
    (fun x _ => (hder x).hasDerivWithinAt)
    (fun x hx => by
      rw [norm_mul, Complex.norm_I, mul_one]
      exact negative_bottom_gaussian_lower_window_mid_high_log_mellin_le δ hδ hx.1 hx.2)
    (x := t₂) (y := t₁) ⟨h₂lo, h₂hi⟩ ⟨h₁lo, h₁hi⟩
  rw [Real.norm_eq_abs] at key
  linarith [key]

end LeanLab.HelfgottMajor.Decomp431a

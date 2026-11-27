import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid_high_lipschitz

/-!
Split of `negative_bottom_gaussian_lower_window_mid_high_main_term_norm_lipschitz` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid_high_lipschitz`.

Source: P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 43, proof of
display 4.43, the main term `Γ(s) (-2 π i δ)^(-s)` of the twisted Gaussian. By the proved reflection
formula `s95_normsq_gamma_half` and `s95_norm_cpow_main`, the norm of the main term at
`1/2 + i t` is `‖w‖^(-1/2) * √(π / cosh (π t)) * exp (a t)` with `w = -2 π i δ` and `a = arg w`,
`|a| ≤ π/2`. The leaf is the Lipschitz bound of the real function `√(π / cosh (π t)) exp (a t)`.

The leaf is OPEN. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: the explicit real comparison behind the main terms, P0014 page 43, proof of display 4.43:
for `|a| ≤ π/2` the function `g(t) = √(π / cosh (π t)) exp (a t)` is Lipschitz on the window from
minus sixty seven forty eighths to minus eleven eighths with constant four times `g(-1)`. Its log
derivative is `a - (π/2) tanh (π t)`, at most π in modulus, and on the window `g(t) ≤ 1.001 g(-1)`.
EASY to MEDIUM: one variable calculus with the mean value theorem. -/
theorem negative_bottom_gaussian_lower_window_mid_high_main_term_real_lipschitz {a : ℝ}
    (ha : |a| ≤ π / 2) {t₁ t₂ : ℝ}
    (h₁lo : -(67 / 48) ≤ t₁) (h₁hi : t₁ ≤ -(11 / 8))
    (h₂lo : -(67 / 48) ≤ t₂) (h₂hi : t₂ ≤ -(11 / 8)) :
    |Real.sqrt (π / Real.cosh (π * t₁)) * Real.exp (a * t₁) -
        Real.sqrt (π / Real.cosh (π * t₂)) * Real.exp (a * t₂)| ≤
      4 * |t₁ - t₂| * (Real.sqrt (π / Real.cosh (π * (-1 : ℝ))) * Real.exp (a * (-1 : ℝ))) := by
  sorry

/-- The norm of the main term in closed form, from `s95_normsq_gamma_half` and
`s95_norm_cpow_main`. -/
theorem negative_bottom_gaussian_lower_window_mid_high_main_term_norm_eq (δ : ℝ) (hδ0 : δ ≠ 0)
    (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (x : ℝ) * Complex.I))‖ =
      ‖-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)‖ ^ (-(1 / 2 : ℝ)) *
        (Real.sqrt (π / Real.cosh (π * x)) *
          Real.exp (Complex.arg (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) * x)) := by
  have hw : -(2 * (π : ℂ) * (δ : ℂ) * Complex.I) ≠ 0 := by
    refine neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_)
      Complex.I_ne_zero)
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast hδ0
  rw [norm_mul, s95_norm_cpow_main _ hw x]
  have hG : ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℝ) * Complex.I)‖ =
      Real.sqrt (π / Real.cosh (π * x)) := by
    rw [← s95_normsq_gamma_half x, Real.sqrt_sq (norm_nonneg _)]
  rw [hG]
  ring

/-- The statement of `negative_bottom_gaussian_lower_window_mid_high_main_term_norm_lipschitz`,
from the closed form of the norm and the real leaf, with `|arg w| ≤ π/2` since `Re w = 0`. -/
theorem negative_bottom_gaussian_lower_window_mid_high_main_term_norm_lipschitz_split (δ : ℝ)
    (hδ0 : δ ≠ 0) {t₁ t₂ : ℝ}
    (h₁lo : -(67 / 48) ≤ t₁) (h₁hi : t₁ ≤ -(11 / 8))
    (h₂lo : -(67 / 48) ≤ t₂) (h₂hi : t₂ ≤ -(11 / 8)) :
    |‖Complex.Gamma ((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t₁ : ℝ) * Complex.I))‖ -
        ‖Complex.Gamma ((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t₂ : ℝ) * Complex.I))‖| ≤
      4 * |t₁ - t₂| * ‖Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I))‖ := by
  rw [negative_bottom_gaussian_lower_window_mid_high_main_term_norm_eq δ hδ0,
    negative_bottom_gaussian_lower_window_mid_high_main_term_norm_eq δ hδ0,
    negative_bottom_gaussian_lower_window_mid_high_main_term_norm_eq δ hδ0]
  set w : ℂ := -(2 * (π : ℂ) * (δ : ℂ) * Complex.I) with hwdef
  have hre : 0 ≤ w.re := by rw [hwdef]; simp
  have harg : |Complex.arg w| ≤ π / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre
  have hR := negative_bottom_gaussian_lower_window_mid_high_main_term_real_lipschitz harg
    h₁lo h₁hi h₂lo h₂hi
  set A := ‖w‖ ^ (-(1 / 2 : ℝ))
  have hA : 0 ≤ A := Real.rpow_nonneg (norm_nonneg _) _
  rw [← mul_sub, abs_mul, abs_of_nonneg hA]
  calc A * |Real.sqrt (π / Real.cosh (π * t₁)) * Real.exp (Complex.arg w * t₁) -
        Real.sqrt (π / Real.cosh (π * t₂)) * Real.exp (Complex.arg w * t₂)|
      ≤ A * (4 * |t₁ - t₂| * (Real.sqrt (π / Real.cosh (π * (-1 : ℝ))) *
          Real.exp (Complex.arg w * (-1 : ℝ)))) := mul_le_mul_of_nonneg_left hR hA
    _ = _ := by ring

end LeanLab.HelfgottMajor.Decomp431a

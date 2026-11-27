import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high
import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_main_term_compare

/-!
Split of `negative_bottom_gaussian_lower_window_high_small_delta` in
`LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_high`.

Route: the Gaussian Mellin transform at real part one half is a parabolic cylinder value,
`Γ(s) e^(z^2/4) D_(-s)(z)` with `z = -2 π i δ`, and for large `|δ|` it is the endpoint main term
`Γ(s) z^(-s)` times one plus a relative error of order `|s|^2 / |z|^2`. This is the large parameter
regime of the treatment of the Mellin transform of the twisted Gaussian `e^(-t^2/2) e(δ t)` in
Helfgott, P0014 and the book. The leaves are the relative error bound for the main term, a
genuine analytic step, and the comparison of the explicit main terms, which is a Gamma reflection
computation and a real inequality.

For `|δ| ≤ 1` the parameter range is cut at one half. On `1/2 ≤ |δ| ≤ 1` the main term route
still works with relative error at most one quarter. On `|δ| ≤ 1/2` the transform is the
everywhere convergent power series in `δ` obtained by expanding `e(δ x)`, whose coefficients are
the untwisted Gaussian moments, given explicitly at `δ = 0` by `2^(s/2 - 1) Γ(s/2)`; the remaining
leaf is the certified evaluation of that series on the window.

Numerical record, S95, mpmath with the closed form checked against direct quadrature: the relative
error of the main term times `δ^2` is at most 0.0395 for `|δ| ≥ 1` and at most 0.058 for
`|δ| ≥ 1/2`, over ordinates between minus eleven eighths and minus one; the ratio in the parent is
at most 1.000845 over `δ` in a grid of step 0.05 on `[-3, 3]` together with `|δ|` up to 1000.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: main term step, large parameter asymptotics of the Mellin transform of the twisted
Gaussian `e^(-t^2/2) e(δ t)`, Helfgott P0014 and the book: for `1/2 ≤ |δ| ≤ 1` and ordinates `u` from minus eleven eighths to minus one, the transform at
`1/2 + i u` is the endpoint term `Γ(s) (-2 π i δ)^(-s)` up to a relative error at most
`1 / (16 δ^2)`. Numerically the error times `δ^2` is at most 0.058 here. HARD. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_mid_main_term_approx (δ : ℝ) (hδ : 1 / 2 ≤ |δ| ∧ |δ| ≤ 1) {u : ℝ} (hlo : -(11 / 8) ≤ u) (hhi : u ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) -
        Complex.Gamma ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (u : ℝ) * Complex.I))‖ ≤
      (1 / (16 * δ ^ 2)) * ‖Complex.Gamma ((1 / 2 : ℂ) + (u : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (u : ℝ) * Complex.I))‖ := by
  sorry

/-- PROVED, was LEAF: comparison of the explicit main terms after the asymptotics of the twisted Gaussian,
Helfgott P0014 and the book, by the reflection formula `|Γ(1/2 + i t)|^2 = π / cosh (π t)` and
`|(-2 π i δ)^(-s)| = (2 π |δ|)^(-1/2) e^(-π t sgn δ / 2)`, so the ratio of the main terms is
`sqrt (cosh π / cosh (π t)) e^(-π (t + 1) sgn δ / 2)`, at most 1.001 on the window. For `1/2 ≤ |δ| ≤ 1`.
MEDIUM. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_mid_main_term_compare (δ : ℝ) (hδ : 1 / 2 ≤ |δ| ∧ |δ| ≤ 1) {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(5 / 4)) :
    (1 + 1 / 4) * ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + (t : ℝ) * Complex.I))‖ ≤
      2 * (1 - 1 / 4) * ‖Complex.Gamma ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) *
          (-(2 * (π : ℂ) * (δ : ℂ) * Complex.I)) ^ (-((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I))‖ := by
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, abs_zero] at hδ; norm_num at hδ
  have he := s95_exp_neg_one_small
  exact s95_main_term_compare_gen δ (1 / 4) hδ0 (by linarith) (by norm_num) (by norm_num) (by nlinarith)

/-- The middle parameter range `1/2 ≤ |δ| ≤ 1` of the parent, proved from the two main term leaves. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_mid (δ : ℝ) (hδ : 1 / 2 ≤ |δ| ∧ |δ| ≤ 1) {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hm : (1 / 2 : ℂ) - Complex.I = (1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hm]
  have hε : 0 ≤ (1 / (16 * δ ^ 2)) ∧ (1 / (16 * δ ^ 2)) ≤ 1 / 4 := by
    have hd : 1 / 4 ≤ δ ^ 2 := by
      have := sq_abs δ; nlinarith [abs_nonneg δ, hδ.1]
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h1 := negative_bottom_gaussian_lower_window_high_small_delta_mid_main_term_approx δ hδ (u := t) (by linarith) (by linarith)
  have h2 := negative_bottom_gaussian_lower_window_high_small_delta_mid_main_term_approx δ hδ (u := -1) (by norm_num) le_rfl
  have h3 := negative_bottom_gaussian_lower_window_high_small_delta_mid_main_term_compare δ hδ hlo hhi
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

/-- PROVED, S95. The untwisted Gaussian Mellin transform in closed form, `∫_0^∞ x^(s-1) e^(-x^2/2) dx =
2^(s/2 - 1) Γ(s/2)` for `Re s > 0`, the value at `δ = 0` used for the twisted Gaussian in
Helfgott P0014 and the book; substitution `x^2/2 = y` in Euler's integral, via `mellin_comp_rpow` and `mellin_comp_mul_left`. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_gamma_zero {s : ℂ} (hs : 0 < s.re) :
    gaussianMellin 0 s = (2 : ℂ) ^ (s / 2 - 1) * Complex.Gamma (s / 2) := by
  have hf : (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e ((0:ℝ) * t)) =
      fun t : ℝ => (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) ((1 / 2 : ℝ) * (t ^ (2 : ℝ))) := by
    funext t
    simp only [zero_mul, e, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, Real.rpow_two]
    congr 2; ring
  have hs2 : 0 < (s / 2).re := by simp; linarith
  unfold gaussianMellin
  rw [hf, mellin_comp_rpow (fun t : ℝ => (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) ((1 / 2 : ℝ) * t)),
    mellin_comp_mul_left (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) _ (by norm_num : (0:ℝ) < 1 / 2),
    ← Complex.GammaIntegral_eq_mellin, show ((2:ℝ):ℂ) = 2 by push_cast; rfl,
    ← Complex.Gamma_eq_integral hs2]
  have h2 : ((1 / 2 : ℝ) : ℂ) ^ (-(s / 2)) = (2 : ℂ) ^ (s / 2) := by
    rw [show ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ by push_cast; ring, Complex.inv_cpow _ _ (by
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by push_cast; rfl, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_ne_zero.symm), Complex.cpow_neg, inv_inv]
  rw [h2, Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one]
  simp only [abs_two, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

section PSPowerSeries

open MeasureTheory

private lemma ps_cpow_shift {t : ℝ} (ht : 0 < t) (s : ℂ) (n : ℕ) :
    (t : ℂ) ^ (s - 1) * (t : ℂ) ^ n = (t : ℂ) ^ (s + n - 1) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have e1 : s + (n : ℂ) - 1 = (s - 1) + (n : ℂ) := by ring
  rw [e1, Complex.cpow_add _ _ ht0, Complex.cpow_natCast]

private lemma ps_norm_cpow {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖(t : ℂ) ^ (s - 1)‖ = t ^ (s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  norm_num [Complex.sub_re]

private lemma ps_exp_series_real (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at h

private lemma ps_exp_series_complex (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) z
  rwa [← Complex.exp_eq_exp_ℂ] at h

private lemma ps_norm_exp_neg (t : ℝ) :
    ‖((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)‖ = Real.exp (-t ^ 2 / 2) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- LEAF: the power series in the twist parameter, from `e(δ x) = Σ (2 π i δ x)^n / n!` and
dominated convergence, the coefficients being the untwisted transforms at `s + n`; the small
parameter expansion of the twisted Gaussian in Helfgott P0014 and the book. MEDIUM. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_power_series (δ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
        gaussianMellin 0 (s + n)) (gaussianMellin δ s) := by
  classical
  set w : ℂ := 2 * (π : ℂ) * (δ : ℂ) * Complex.I with hw
  let F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (s - 1) * (w ^ n / (n.factorial : ℂ) * (t : ℂ) ^ n *
    ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ))
  let ff : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * (((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * e (δ * t))
  let bd : ℕ → ℝ → ℝ := fun n t => ‖w‖ ^ n / (n.factorial : ℝ) *
    (t ^ (s.re - 1) * (t ^ (n : ℝ) * Real.exp (-t ^ 2 / 2)))
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Set.Ioi (0 : ℝ)) := by
      intro x hx
      exact (Complex.continuousAt_ofReal_cpow_const x (s - 1) (Or.inr (ne_of_gt hx))).continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)) (Set.Ioi (0 : ℝ)) :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).continuousOn
    exact h1.mul ((continuousOn_const.mul ((Complex.continuous_ofReal.pow n).continuousOn)).mul h2)
  have hbound : ∀ n : ℕ, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ‖F n t‖ ≤ bd n t := by
    intro n
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hnorm : ‖F n t‖ = ‖w‖ ^ n / (n.factorial : ℝ) *
        (t ^ (s.re - 1) * (t ^ (n : ℝ) * Real.exp (-t ^ 2 / 2))) := by
      simp only [F]
      rw [norm_mul, norm_mul, norm_mul, ps_norm_cpow ht0, norm_div, norm_pow, Complex.norm_natCast,
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, ps_norm_exp_neg,
        Real.rpow_natCast]
      ring
    rw [hnorm]
  have hbsumm : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), Summable (fun n : ℕ => bd n t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hfac : ∀ n : ℕ, bd n t = (t ^ (s.re - 1) * Real.exp (-t ^ 2 / 2)) *
        ((‖w‖ * t) ^ n / (n.factorial : ℝ)) := by
      intro n
      simp only [bd]
      rw [mul_pow, Real.rpow_natCast]
      ring
    simp only [hfac]
    exact Summable.mul_left _ (Real.summable_pow_div_factorial (‖w‖ * t))
  have hGint : Integrable (fun t : ℝ => t ^ (s.re - 1) *
      (Real.exp (-t ^ 2 / 2) * Real.exp (‖w‖ * t))) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hdom : Integrable (fun t : ℝ => Real.exp (‖w‖ ^ 2) *
        (t ^ (s.re - 1) * Real.exp (-t ^ 2 / 4))) (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hbase := (integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 4 : ℝ)) (by norm_num)
        (s := s.re - 1) (by linarith)).const_mul (Real.exp (‖w‖ ^ 2))
      have hshape : (fun t : ℝ => Real.exp (‖w‖ ^ 2) *
          (t ^ (s.re - 1) * Real.exp (-(1 / 4 : ℝ) * t ^ 2))) =
          fun t : ℝ => Real.exp (‖w‖ ^ 2) * (t ^ (s.re - 1) * Real.exp (-t ^ 2 / 4)) := by
        funext t; ring_nf
      rw [hshape] at hbase
      exact hbase
    refine Integrable.mono' hdom ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      have h1 : ContinuousOn (fun t : ℝ => t ^ (s.re - 1)) (Set.Ioi (0 : ℝ)) := by
        intro x hx
        exact (Real.continuousAt_rpow_const x (s.re - 1) (Or.inl (ne_of_gt hx))).continuousWithinAt
      have h2 : ContinuousOn (fun t : ℝ => Real.exp (-t ^ 2 / 2)) (Set.Ioi (0 : ℝ)) :=
        (Real.continuous_exp.comp (by fun_prop)).continuousOn
      have h3 : ContinuousOn (fun t : ℝ => Real.exp (‖w‖ * t)) (Set.Ioi (0 : ℝ)) :=
        (Real.continuous_exp.comp (by fun_prop)).continuousOn
      exact h1.mul (h2.mul h3)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hA : (0 : ℝ) ≤ t ^ (s.re - 1) := Real.rpow_nonneg ht0.le _
      have hB : (0 : ℝ) ≤ Real.exp (-t ^ 2 / 2) := (Real.exp_pos _).le
      have hC : (0 : ℝ) ≤ Real.exp (‖w‖ * t) := (Real.exp_pos _).le
      have hkey : Real.exp (-t ^ 2 / 2) * Real.exp (‖w‖ * t) ≤
          Real.exp (‖w‖ ^ 2) * Real.exp (-t ^ 2 / 4) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (‖w‖ - t / 2), sq_nonneg ‖w‖]
      have hnn : (0 : ℝ) ≤ t ^ (s.re - 1) * (Real.exp (-t ^ 2 / 2) * Real.exp (‖w‖ * t)) :=
        mul_nonneg hA (mul_nonneg hB hC)
      rw [Real.norm_of_nonneg hnn]
      calc t ^ (s.re - 1) * (Real.exp (-t ^ 2 / 2) * Real.exp (‖w‖ * t))
          ≤ t ^ (s.re - 1) * (Real.exp (‖w‖ ^ 2) * Real.exp (-t ^ 2 / 4)) :=
            mul_le_mul_of_nonneg_left hkey hA
        _ = Real.exp (‖w‖ ^ 2) * (t ^ (s.re - 1) * Real.exp (-t ^ 2 / 4)) := by ring
  have hbdint : Integrable (fun t : ℝ => ∑' n : ℕ, bd n t) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have heq : (fun t : ℝ => ∑' n : ℕ, bd n t) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ => t ^ (s.re - 1) * (Real.exp (-t ^ 2 / 2) * Real.exp (‖w‖ * t)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hfac : ∀ n : ℕ, bd n t = (t ^ (s.re - 1) * Real.exp (-t ^ 2 / 2)) *
          ((‖w‖ * t) ^ n / (n.factorial : ℝ)) := by
        intro n
        simp only [bd]
        rw [mul_pow, Real.rpow_natCast]
        ring
      simp only [hfac, tsum_mul_left, (ps_exp_series_real (‖w‖ * t)).tsum_eq]
      ring
    exact hGint.congr heq.symm
  have hlim : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), HasSum (fun n : ℕ => F n t) (ff t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hA : HasSum (fun n : ℕ => (w * (t : ℂ)) ^ n / (n.factorial : ℂ)) (e (δ * t)) := by
      have h := ps_exp_series_complex (w * (t : ℂ))
      have h1 : w * (t : ℂ) = 2 * (π : ℂ) * Complex.I * ((δ * t : ℝ) : ℂ) := by
        rw [hw]; push_cast; ring
      have h2 : e (δ * t) = Complex.exp (2 * (π : ℂ) * Complex.I * ((δ * t : ℝ) : ℂ)) := by
        rfl
      simpa only [h1, h2] using h
    have h2 : ∀ n : ℕ, ((t : ℂ) ^ (s - 1) * ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)) *
        ((w * (t : ℂ)) ^ n / (n.factorial : ℂ)) = F n t := by
      intro n
      simp only [F]
      rw [mul_pow]
      ring
    have h3 : ((t : ℂ) ^ (s - 1) * ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)) * e (δ * t) = ff t := by
      simp only [ff]
      ring
    have h4 := hA.mul_left ((t : ℂ) ^ (s - 1) * ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ))
    rw [funext h2, h3] at h4
    exact h4
  have key := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (F := F) (f := ff) bd hFmeas hbound hbsumm hbdint hlim
  have hInt : ∀ n : ℕ, (∫ t : ℝ, F n t ∂(volume.restrict (Set.Ioi (0 : ℝ)))) =
      w ^ n / (n.factorial : ℂ) * gaussianMellin 0 (s + n) := by
    intro n
    have hgm : gaussianMellin 0 (s + n) =
        ∫ t : ℝ, (t : ℂ) ^ (s + n - 1) * ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)
          ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
      rw [gaussianMellin, mellin]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      simp [e, smul_eq_mul]
    rw [hgm]
    have hstep : (∫ t : ℝ, F n t ∂(volume.restrict (Set.Ioi (0 : ℝ)))) =
        ∫ t : ℝ, (w ^ n / (n.factorial : ℂ)) *
          ((t : ℂ) ^ (s - 1) * ((t : ℂ) ^ n * ((Real.exp (-t ^ 2 / 2) : ℝ) : ℂ)))
          ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      simp only [F]
      ring
    rw [hstep, MeasureTheory.integral_const_mul]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [← mul_assoc, ps_cpow_shift ht s n]
  have hval : (∫ t : ℝ, ff t ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = gaussianMellin δ s := by
    rw [gaussianMellin, mellin]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [ff, smul_eq_mul]
  rw [hval, funext hInt] at key
  simpa only [hw] using key

end PSPowerSeries


/-- LEAF: certified evaluation of the power series of the previous leaves for `|δ| ≤ 1/2` on the
window from minus eleven eighths to minus five quarters: the series at `1/2 + i t` has norm at
most twice the series at `1/2 - i`. Needs an explicit tail bound from `|Γ(σ + i τ)| ≤ Γ(σ)` and
interval evaluation of finitely many Gamma values; numerically the ratio is at most 0.97 for
`|δ| ≤ 1/2`. HARD. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_series_compare (δ : ℝ) (hδ : |δ| ≤ 1 / 2) {t : ℝ} (hlo : -(11 / 8) ≤ t)
    (hhi : t ≤ -(5 / 4)) :
    ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2 - 1) * Complex.Gamma ((((1 / 2 : ℂ) + (t : ℝ) * Complex.I) + n) / 2))‖ ≤
      2 * ‖∑' n : ℕ, (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((((1 / 2 : ℂ) - Complex.I) + n) / 2 - 1) * Complex.Gamma ((((1 / 2 : ℂ) - Complex.I) + n) / 2))‖ := by
  sorry

/-- Assembly of `negative_bottom_gaussian_lower_window_high_small_delta`, exactly its statement: the series route for `|δ| ≤ 1/2`, with the
closed form at `δ = 0` for the coefficients, and the main term route for `1/2 < |δ| ≤ 1`. -/
theorem negative_bottom_gaussian_lower_window_high_small_delta_split (δ : ℝ) (hδ : |δ| ≤ 1)
    {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rcases le_or_gt |δ| (1 / 2) with hs | hs
  · have key : ∀ S : ℂ, 0 < S.re → gaussianMellin δ S = ∑' n : ℕ,
        (2 * (π : ℂ) * (δ : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) *
          ((2 : ℂ) ^ ((S + n) / 2 - 1) * Complex.Gamma ((S + n) / 2)) := by
      intro S hS
      rw [← (negative_bottom_gaussian_lower_window_high_small_delta_power_series δ hS).tsum_eq]
      congr 1
      funext n
      rw [negative_bottom_gaussian_lower_window_high_small_delta_gamma_zero (s := S + n) (by simp; positivity)]
    rw [key _ (by simp), key _ (by simp)]
    exact negative_bottom_gaussian_lower_window_high_small_delta_series_compare δ hs hlo hhi
  · exact negative_bottom_gaussian_lower_window_high_small_delta_mid δ ⟨le_of_lt hs, hδ⟩ hlo hhi

end LeanLab.HelfgottMajor.Decomp431a

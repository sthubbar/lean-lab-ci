/-
CITED WALL, step initial_segment_bound of Decomp639Contour, session CLOUD-cited-initial_segment_bound,
2026-11-20. P0014, Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4,
pages 24 and 25, displays 3.58 to 3.63, and Appendix page 67, display A.33.

DECISION. The leaf `Decomp639Contour.initial_segment_bound` rests on two different inputs.
1. Display A.33 on page 67 is a computer check, the bisection method on [0.1, 25] with
   24 iterations, plus hand bounds for small and large rho. It becomes the named hypothesis
   `HelfgottA33` below. A float scan of 400001 points on [1e-6, 1e6] gives the maxima
   0.0763896 near rho = 3.60 and 0.49929 at rho = 1e6, in line with the paper.
2. The rest is the integration by parts of pages 24 and 25 on the segment C1. It stays one
   LEAF, `initial_ibp_bound`, stated with the exact exponent l r / sqrt 2 of display 3.60.
The two consequences of A.33 used on page 24, the phase cost and display 3.61, are proved
here from the hypothesis, and `initial_segment_bound_of_A33` assembles the leaf statement
from the hypothesis and the new LEAF with no sorry.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottMajor.Decomp639Contour

namespace LeanLab.HelfgottMajor.DQInitialSegmentBound

open Real MeasureTheory Set LeanLab.HelfgottMajor.Decomp511a
  LeanLab.HelfgottMajor.Decomp639Contour

/-- NAMED HYPOTHESIS, cited computation. P0014 page 67, display A.33, both lines:
`max_{ρ ≥ 0} (c0 - 1/√2)/(√2 c1 ρ) ≤ 0.0763896` and `sup_{ρ ≥ 0} (c0 - 1/√2)/(c1 √ρ) ≤ 1/2`,
obtained there by the bisection method on [0.1, 25] together with hand bounds for
rho at most 0.1 and at least 25. Stated for positive rho, the only range used. -/
def HelfgottA33 : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    (c0 ρ - 1 / sqrt 2) / (sqrt 2 * c1 ρ * ρ) ≤ 0.0763896 ∧
    (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) ≤ 1 / 2

/-- P0014 page 24, the display after 3.60: by A.33, `ℓ r₋ / √2 ≤ 0.07639 ℓ² ρ`, and
`ℓ² ρ = 4 |τ|`, so the phase cost is at most `0.30556 |τ|`. CONDITIONAL ON `HelfgottA33`. -/
theorem initialRadius_phase_of_A33 (hA : HelfgottA33) (δ τ : ℝ) (hδ : δ ≠ 0)
    (hτ : 0 < |τ|) :
    ell δ * initialRadius δ τ / sqrt 2 ≤ 0.30556 * |τ| := by
  have hρ := rho_pos δ τ hδ hτ
  have hc := c1_pos _ hρ
  have hL := ell_pos δ hδ
  have hs : 0 < sqrt (2:ℝ) := by positivity
  have hs2 : sqrt (2:ℝ) * sqrt 2 = 2 := mul_self_sqrt (by norm_num)
  have hX := (hA _ hρ).1
  rw [div_le_iff₀ (by positivity)] at hX
  have he := ell_sq_mul_rho δ τ hδ
  have hkey : ell δ * initialRadius δ τ / sqrt 2 =
      ell δ ^ 2 * (c0 (rho δ τ) - 1 / sqrt 2) / (c1 (rho δ τ) * sqrt 2) := by
    unfold initialRadius
    field_simp
  have hb : ell δ ^ 2 * (c0 (rho δ τ) - 1 / sqrt 2) / (c1 (rho δ τ) * sqrt 2) ≤
      ell δ ^ 2 * (0.0763896 * (sqrt 2 * c1 (rho δ τ) * rho δ τ)) /
        (c1 (rho δ τ) * sqrt 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  have hc2 : ell δ ^ 2 * (0.0763896 * (sqrt 2 * c1 (rho δ τ) * rho δ τ)) /
        (c1 (rho δ τ) * sqrt 2) = 0.0763896 * (ell δ ^ 2 * rho δ τ) := by
    field_simp
  rw [hkey]
  calc _ ≤ _ := hb
    _ = _ := hc2
    _ ≤ _ := by rw [he]; nlinarith

/-- P0014 page 24, display 3.61: `r₋ ≤ √ρ ℓ / 2 ≤ √τ`, from 3.58 and the second line of A.33.
CONDITIONAL ON `HelfgottA33`. -/
theorem initialRadius_le_sqrt_of_A33 (hA : HelfgottA33) (δ τ : ℝ) (hδ : δ ≠ 0)
    (hτ : 0 < |τ|) :
    initialRadius δ τ ≤ sqrt |τ| := by
  have hρ := rho_pos δ τ hδ hτ
  have hc := c1_pos _ hρ
  have hL := ell_pos δ hδ
  have hsr : 0 < sqrt (rho δ τ) := sqrt_pos.mpr hρ
  have hX := (hA _ hρ).2
  rw [div_le_iff₀ (by positivity)] at hX
  have hm := ell_mul_sqrt_rho δ τ hδ
  have hkey : initialRadius δ τ = ell δ / c1 (rho δ τ) * (c0 (rho δ τ) - 1 / sqrt 2) := rfl
  rw [hkey]
  calc _ ≤ ell δ / c1 (rho δ τ) * (1 / 2 * (c1 (rho δ τ) * sqrt (rho δ τ))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = ell δ * sqrt (rho δ τ) / 2 := by field_simp
    _ = _ := by rw [hm]; ring

/-- P0014 page 24 before display 3.59: the direction w = (1 + i)/√2, conjugated for negative
height, in real and imaginary parts. -/
theorem rayDirection_explicit (τ : ℝ) :
    rayDirection τ = ((1 / sqrt 2 : ℝ) : ℂ) +
      (((if 0 ≤ τ then 1 else -1) / sqrt 2 : ℝ) : ℂ) * Complex.I := by
  unfold rayDirection
  split_ifs <;> push_cast <;> ring

/-- P0014 page 24 before display 3.59: arg w = ±π/4 for the ray direction. -/
theorem rayDirection_arg (τ : ℝ) :
    Complex.arg (rayDirection τ) = if 0 ≤ τ then π / 4 else -(π / 4) := by
  rw [rayDirection_eq_exp, Complex.exp_mul_I]
  apply Complex.arg_cos_add_sin_mul_I
  split_ifs <;> constructor <;> linarith [pi_pos]

/-- P0014 page 24, display 3.60: on the ray, the real part of `-z²/2 + 2πiδz` with `z = r w`
is `-2πδ r · Im w`, since `w²` is purely imaginary. -/
theorem ray_exponent_re (δ τ r : ℝ) :
    (-((r:ℂ) * rayDirection τ) ^ 2 / 2 + 2 * π * Complex.I * δ * (r * rayDirection τ)).re =
      -(2 * π * δ * r * ((if 0 ≤ τ then 1 else -1) / sqrt 2)) := by
  rw [rayDirection_explicit]
  have h2 : sqrt (2:ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hs : sqrt (2:ℝ) ≠ 0 := by positivity
  split_ifs <;>
  · simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
    field_simp
    rw [h2]; ring

/-- P0014 page 24, display 3.60: on C1, `|z^{s-1} e^{-z²/2} e(δz)| = r^{σ-1} e^{ℓ r/√2 - π|τ|/4}`
when `δ τ < 0`, for every exponent with imaginary part τ. -/
theorem ray_kernel_norm (δ τ : ℝ) (z : ℂ) (r : ℝ) (hr : 0 < r) (hz : z.im = τ)
    (hsign : δ * τ < 0) :
    ‖contourKernel δ z (r * rayDirection τ) * rayDirection τ‖ =
      r ^ (z.re - 1) * exp (ell δ * r / sqrt 2 - π / 4 * |τ|) := by
  have hw := rayDirection_norm τ
  have hne : (r:ℂ) * rayDirection τ ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast hr.ne') ?_
    intro h; rw [h, norm_zero] at hw; norm_num at hw
  unfold contourKernel
  rw [norm_mul, hw, mul_one, norm_mul, Complex.norm_cpow_of_ne_zero hne, Complex.norm_exp,
    ray_exponent_re, norm_mul, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_one,
    Complex.arg_real_mul _ hr, rayDirection_arg]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, hz]
  rw [div_eq_mul_inv, ← exp_neg, mul_assoc, ← exp_add]
  congr 2
  unfold ell
  rcases lt_or_gt_of_ne (show τ ≠ 0 by rintro rfl; simp at hsign) with h | h
  · have hd : 0 < δ := by nlinarith
    simp only [show ¬ (0 ≤ τ) from not_le.mpr h, ↓reduceIte]
    rw [abs_of_neg h, abs_of_pos hd]; ring
  · have hd : δ < 0 := by nlinarith
    simp only [h.le, ↓reduceIte]
    rw [abs_of_pos h, abs_of_neg hd]; ring

/-- P0014 page 25, after display 3.63: `∫_0^a A e^{L r/√2 - K} dr` in closed form. -/
theorem ray_exp_integral (L A K a : ℝ) (hL : 0 < L) (ha : 0 ≤ a) :
    ∫ r in Ioo 0 a, A * exp (L * r / sqrt 2 - K) =
      A * (sqrt 2 / L) * (exp (L * a / sqrt 2 - K) - exp (-K)) := by
  have hs : 0 < sqrt (2:ℝ) := by positivity
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha]
  have hD : ∀ x ∈ uIcc 0 a, HasDerivAt
      (fun r => A * (sqrt 2 / L) * exp (L * r / sqrt 2 - K))
      (A * exp (L * x / sqrt 2 - K)) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => L * r / sqrt 2 - K) (L / sqrt 2) x := by
      simpa using (((hasDerivAt_id x).const_mul L).div_const (sqrt 2)).sub_const K
    convert (h1.exp).const_mul (A * (sqrt 2 / L)) using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD
    ((by fun_prop : Continuous fun r : ℝ => A * exp (L * r / sqrt 2 - K)).intervalIntegrable _ _)]
  simp only [mul_zero, zero_div, zero_sub]
  ring

/-- PROVED, formerly the LEAF of this file. P0014 pages 24 and 25, displays 3.59, 3.60 and 3.63
with the bounds after 3.63.
Integration by parts on C1 from 0 to `w r₋`: the boundary term is at most
`r₋^σ / τ · e^{ℓ r₋ / √2 - π τ / 4}`, and the two integrals of display 3.63 are at most
`(r₋^{σ+2} + √2 r₋^σ) / τ · e^{ℓ r₋ / √2 - π τ / 4}` by `|s| ≥ τ` and
`∫_0^{r₋} e^{ℓ t / √2} dt ≤ min(√2 / ℓ, r₋) e^{ℓ r₋ / √2}`.
The exponent keeps the `√2` of display 3.60; the printed `ℓ r₋ / 2` on page 25 is a typo
that the paper's final line does not use. -/
theorem initial_ibp_bound (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖initialIntegral δ s‖ ≤
      (initialRadius δ s.im ^ (s.re + 2) + (1 + sqrt 2) * initialRadius δ s.im ^ s.re) /
        |s.im| * exp (ell δ * initialRadius δ s.im / sqrt 2 - π / 4 * |s.im|) := by
  set τ := s.im with hτdef
  set σ := s.re with hσdef
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |τ| := by linarith
  set a := initialRadius δ τ with hadef
  have ha : 0 < a := initialRadius_pos δ τ hd hτ
  set w := rayDirection τ with hwdef
  have hL : 0 < ell δ := ell_pos δ hd
  have hs2 : 0 < sqrt (2:ℝ) := by positivity
  set E := exp (ell δ * a / sqrt 2 - π / 4 * |τ|) with hE
  have hE0 : 0 < E := exp_pos _
  have hker : ∀ (z : ℂ), z.im = τ → ∀ r ∈ Ioo 0 a,
      ‖contourKernel δ z (r * w) * w‖ ≤ r ^ (z.re - 1) * exp (ell δ * r / sqrt 2 - π / 4 * |τ|) :=
    fun z hz r hr => (ray_kernel_norm δ τ z r hr.1 hz hsign).le
  -- boundary term
  have hB : ‖contourKernel δ s (a * w) * (a * w)‖ ≤ a ^ σ * E := by
    have h := ray_kernel_norm δ τ s a ha rfl hsign
    have hm : ‖contourKernel δ s (a * w) * (a * w)‖ =
        ‖contourKernel δ s (a * w) * w‖ * a := by
      rw [show contourKernel δ s (a * w) * (a * w) = (contourKernel δ s (a * w) * w) * a by ring,
        norm_mul (contourKernel δ s (a * w) * w), Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    rw [hm, h, mul_right_comm, ← rpow_add_one ha.ne', sub_add_cancel]
  -- the s + 2 integral
  have hI2 : ‖∫ r in Ioo 0 a, contourKernel δ (s + 2) (r * w) * w‖ ≤ a ^ (σ + 2) * E := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo 0 a)
      (C := a ^ (σ + 1) * E) measure_Ioo_lt_top (fun r hr => by
        refine (hker (s + 2) (by simp [hτdef]) r hr).trans ?_
        have hre : (s + 2).re - 1 = σ + 1 := by simp [hσdef]; ring
        rw [hre]
        apply mul_le_mul (rpow_le_rpow hr.1.le hr.2.le (by linarith))
          (exp_le_exp.mpr ?_) (exp_pos _).le (by positivity)
        have := mul_le_mul_of_nonneg_left hr.2.le hL.le
        have := div_le_div_of_nonneg_right this hs2.le
        linarith)
    rw [volume_real_Ioo_of_le ha.le, sub_zero] at h
    calc _ ≤ _ := h
      _ = a ^ (σ + 1 + 1) * E := by rw [rpow_add_one ha.ne' (σ + 1)]; ring
      _ = _ := by rw [show σ + 1 + 1 = σ + 2 by ring]
  -- the s + 1 integral
  have hI1 : ‖(2 * π * Complex.I * δ) *
      ∫ r in Ioo 0 a, contourKernel δ (s + 1) (r * w) * w‖ ≤ sqrt 2 * a ^ σ * E := by
    have hc : ‖(2 * π * Complex.I * δ : ℂ)‖ = ell δ := by
      unfold ell
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
    have hg : IntegrableOn (fun r : ℝ => a ^ σ * exp (ell δ * r / sqrt 2 - π / 4 * |τ|))
        (Ioo 0 a) :=
      (by fun_prop : Continuous fun r : ℝ => a ^ σ * exp (ell δ * r / sqrt 2 - π / 4 * |τ|)
        ).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have h := norm_integral_le_of_norm_le hg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      refine (hker (s + 1) (by simp [hτdef]) r hr).trans ?_
      have hre : (s + 1).re - 1 = σ := by simp [hσdef]
      rw [hre]
      exact mul_le_mul_of_nonneg_right (rpow_le_rpow hr.1.le hr.2.le hσ0.le) (exp_pos _).le)
    rw [ray_exp_integral (ell δ) (a ^ σ) (π / 4 * |τ|) a hL ha.le, ← hE] at h
    rw [norm_mul, hc]
    calc _ ≤ ell δ * (a ^ σ * (sqrt 2 / ell δ) *
          (E - exp (-(π / 4 * |τ|)))) :=
          mul_le_mul_of_nonneg_left h hL.le
      _ = sqrt 2 * a ^ σ * (E - exp (-(π / 4 * |τ|))) := by field_simp
      _ ≤ _ := by
          have : 0 ≤ sqrt 2 * a ^ σ := by positivity
          nlinarith [exp_pos (-(π / 4 * |τ|))]
  -- assemble
  have hrec := finite_ray_recurrence δ τ s a hσ0 ha
  have hsn : |τ| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hmain : ‖s‖ * ‖initialIntegral δ s‖ ≤
      (a ^ σ + a ^ (σ + 2) + sqrt 2 * a ^ σ) * E := by
    rw [← norm_mul]
    unfold initialIntegral
    rw [hrec]
    calc _ ≤ ‖contourKernel δ s (a * w) * (a * w) +
            ∫ r in Ioo 0 a, contourKernel δ (s + 2) (r * w) * w‖ +
          ‖(2 * π * Complex.I * δ) *
            ∫ r in Ioo 0 a, contourKernel δ (s + 1) (r * w) * w‖ := norm_sub_le _ _
      _ ≤ ‖contourKernel δ s (a * w) * (a * w)‖ +
            ‖∫ r in Ioo 0 a, contourKernel δ (s + 2) (r * w) * w‖ +
          ‖(2 * π * Complex.I * δ) *
            ∫ r in Ioo 0 a, contourKernel δ (s + 1) (r * w) * w‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ a ^ σ * E + a ^ (σ + 2) * E + sqrt 2 * a ^ σ * E := by gcongr
      _ = _ := by ring
  have hN := norm_nonneg (initialIntegral δ s)
  rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
  calc ‖initialIntegral δ s‖ * |τ| ≤ ‖s‖ * ‖initialIntegral δ s‖ := by nlinarith
    _ ≤ _ := hmain
    _ = _ := by ring

/-- P0014 page 25, the conclusion after display 3.63, assembled with no sorry from the
named hypothesis A.33 and the LEAF `initial_ibp_bound`. The statement after the hypothesis
is word for word that of `Decomp639Contour.initial_segment_bound`.
CONDITIONAL ON `HelfgottA33` and on the LEAF `initial_ibp_bound`. -/
theorem initial_segment_bound_of_A33 (hA : HelfgottA33) (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖initialIntegral δ s‖ ≤ firstCoefficient s.re |s.im| *
      exp (-0.4798 * |s.im|) := by
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |s.im| := by linarith
  have hr := initialRadius_pos δ s.im hd hτ
  have hphase := initialRadius_phase_of_A33 hA δ s.im hd hτ
  have hrad := initialRadius_le_sqrt_of_A33 hA δ s.im hd hτ
  have hpre := initial_radius_prefactor s.re |s.im| (initialRadius δ s.im) hσ0.le hτ hr hrad
  have hexp := initial_phase_cost |s.im| (ell δ) (initialRadius δ s.im) (abs_nonneg _) hphase
  have hpre0 : 0 ≤ (initialRadius δ s.im ^ (s.re + 2) +
      (1 + sqrt 2) * initialRadius δ s.im ^ s.re) / |s.im| := by positivity
  have hF0 : 0 ≤ firstCoefficient s.re |s.im| := by
    unfold firstCoefficient; positivity
  calc _ ≤ _ := initial_ibp_bound δ s hσ0 hσ1 ht hsign
    _ ≤ _ := mul_le_mul hpre hexp (exp_pos _).le hF0

/-- Twin check: the conditional assembly has exactly the type of the sealed leaf
`Decomp639Contour.initial_segment_bound` once the hypothesis is supplied. -/
theorem initial_segment_bound_twin (hA : HelfgottA33) :
    type_of% @Decomp639Contour.initial_segment_bound :=
  initial_segment_bound_of_A33 hA

end LeanLab.HelfgottMajor.DQInitialSegmentBound

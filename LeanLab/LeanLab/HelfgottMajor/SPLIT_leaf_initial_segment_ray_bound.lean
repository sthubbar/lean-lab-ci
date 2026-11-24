import LeanLab.HelfgottMajor.SPLIT_leaf_lower_contour_estimate

/-!
Split of `leaf_initial_segment_ray_bound` of
`HelfgottMajor/SPLIT_leaf_lower_contour_estimate.lean`.

Source: P0014, the estimate of the first contour piece `C₁`, displays 3.59 to 3.63
and the unnumbered conclusion after 3.63, page 24 to 25.  There the segment goes
from `0` to `w r₋` with `w = (1 + i) / sqrt 2`, the modulus on the segment is
`exp (-ℜ φ (t w)) t ^ (σ - 1)` with `ℜ φ (t w) = -ℓ t / sqrt 2 + π τ / 4`, display 3.60,
and the paper uses the length bound `r₋ ≤ sqrt τ`, display 3.61.  It then splits:

* `σ ≥ 1`, display 3.62: bound the integrand by its modulus, giving `τ ^ (σ / 2)`;
  on the strip `0 < σ ≤ 1` this is the single value `σ = 1`;
* `0 ≤ σ < 1`: an integration by parts, display 3.63, giving the factor
  `1 + (1 + sqrt 2) / τ`.

The parent leaf does not assume the paper's length bound `r ≤ sqrt |im s|`; it
assumes only the phase condition.  So the cut below has three leaves: the two cases
of the paper under `r ≤ sqrt |im s|`, and the long segment case `sqrt |im s| < r`,
which the paper never needs because its `r₋` obeys 3.61.  The long case is still
expected true: past the saddle `x = sqrt τ` the phase derivative grows like `x`, so
an integration by parts at the far endpoint gives a term of size
`r ^ (σ - 2) * exp (-0.4798 τ)`, but it is not a step of the paper, and the leaf says
so.  The assembly is a case split on `r ≤ sqrt |im s|` and on `s.re = 1`.
-/

namespace LeanLab.HelfgottMajor.Decomp511a
open Real SplitGaussian123 Filter
open scoped Topology

/-- The rotation base of the first contour piece is `exp (i π / 4)`, P0014 page 24, display 3.59. -/
theorem s95_rot_base_eq :
    (((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ)) =
      Complex.cos ((π / 4 : ℝ) : ℂ) + Complex.sin ((π / 4 : ℝ) : ℂ) * Complex.I := by
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext
  · simp [Complex.div_re]
  · simp [Complex.div_im]

/-- `|exp (i π / 4) ^ s| = exp (-π im s / 4)`, the factor `e^(-π τ / 4)` of display 3.60. -/
theorem s95_norm_rot_base_cpow (s : ℂ) :
    ‖(((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ)) ^ s‖ = exp (-(π / 4) * s.im) := by
  rw [s95_rot_base_eq]
  have hne : Complex.cos ((π / 4 : ℝ) : ℂ) + Complex.sin ((π / 4 : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h; have := Complex.norm_cos_add_sin_mul_I (π / 4); rw [h, norm_zero] at this; norm_num at this
  rw [Complex.norm_cpow_of_ne_zero hne, Complex.norm_cos_add_sin_mul_I,
    Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
    Real.one_rpow, one_div, ← Real.exp_neg]
  ring_nf

/-- The case `s.re = 1` of the first contour piece, P0014 page 24, displays 3.60 to 3.62: on the
ray the integrand has modulus `exp (-2 π δ x / sqrt 2)`, the base gives `exp (-π τ / 4)`, the phase
condition gives `r * exp (-0.4798 τ)`, and `r ≤ sqrt τ ≤` the first coefficient. Proved. -/
theorem s95_leaf_ray_short_sigma_one (δ : ℝ) (s : ℂ) (r : ℝ)
    (hσ1 : s.re = 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) (hspos : 0 < s.im) (hr : 0 < r) (hrs : r ≤ sqrt |s.im|)
    (hexp : 0.4798 * |s.im| + 2 * π * |δ| * r / Real.sqrt 2 ≤ π / 4 * |s.im|) :
    ‖(((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
        (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
          LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t)‖ ≤
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  set τ := s.im with hτ
  have hτa : |τ| = τ := abs_of_pos hspos
  rw [hτa] at ht hrs hexp ⊢
  set C := exp (2 * π * |δ| * r / Real.sqrt 2) with hC
  have hbound : ∀ x ∈ Set.Ioc (0 : ℝ) r,
      ‖LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s x‖ ≤ C := by
    intro x hx
    rw [LeanLab.HelfgottMajor.Decomp511b.rotatedKernel_norm δ (π / 4) s x hx.1, hσ1, sub_self,
      Real.rpow_zero, one_mul, hC]
    apply Real.exp_le_exp.mpr
    have hc : Real.cos (2 * (π / 4)) = 0 := by rw [show 2 * (π / 4) = π / 2 by ring]; exact Real.cos_pi_div_two
    rw [hc, Real.sin_pi_div_four]
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hxr : x ≤ r := hx.2
    have hx0 : 0 < x := hx.1
    have key : -(2 * π * δ * (Real.sqrt 2 / 2) * x) ≤ 2 * π * |δ| * r / Real.sqrt 2 := by
      rw [le_div_iff₀ hs2]
      have h1 : -(δ * x) ≤ |δ| * r := by
        have := neg_abs_le δ
        nlinarith [abs_nonneg δ]
      have e : -(2 * π * δ * (Real.sqrt 2 / 2) * x) * Real.sqrt 2 = 2 * π * (-(δ * x)) := by
        linear_combination (-(π * δ * x)) * hs
      rw [e]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * π)
      linarith
    linarith [key]
  have hint : ‖∫ t : ℝ in Set.Ioc (0 : ℝ) r,
      LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t‖ ≤ C * r := by
    have := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := MeasureTheory.volume)
      (s := Set.Ioc (0 : ℝ) r) measure_Ioc_lt_top hbound
    simpa [MeasureTheory.Measure.real, Real.volume_Ioc, hr.le] using this
  rw [norm_mul, s95_norm_rot_base_cpow, hσ1]
  have hstep : exp (-(π / 4) * τ) * (C * r) ≤ r * exp (-0.4798 * τ) := by
    rw [hC, show exp (-(π / 4) * τ) * (exp (2 * π * |δ| * r / Real.sqrt 2) * r) =
      r * exp (-(π / 4) * τ + 2 * π * |δ| * r / Real.sqrt 2) by rw [Real.exp_add]; ring]
    apply mul_le_mul_of_nonneg_left _ hr.le
    apply Real.exp_le_exp.mpr; linarith
  have hfc : Real.sqrt τ ≤ firstCoefficient 1 τ := by
    unfold firstCoefficient
    rw [show (1 : ℝ) / 2 = (1 / 2 : ℝ) from rfl, ← Real.sqrt_eq_rpow]
    have h0 : 0 ≤ (1 + Real.sqrt 2) / τ := by positivity
    have hsq : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
    nlinarith
  calc exp (-(π / 4) * τ) * ‖∫ t : ℝ in Set.Ioc (0 : ℝ) r,
        LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t‖
      ≤ exp (-(π / 4) * τ) * (C * r) := mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ ≤ r * exp (-0.4798 * τ) := hstep
    _ ≤ Real.sqrt τ * exp (-0.4798 * τ) := mul_le_mul_of_nonneg_right hrs (Real.exp_pos _).le
    _ ≤ firstCoefficient 1 τ * exp (-0.4798 * τ) := mul_le_mul_of_nonneg_right hfc (Real.exp_pos _).le

/-- PROVED, was LEAF: P0014 page 24, display 3.62, the case `σ ≥ 1` of the first contour piece,
which on the strip is `s.re = 1`.  With `r ≤ sqrt |im s|`, display 3.61, the
integrand of the ray integral times `w ^ s` has modulus
`exp (2 * π * |δ| * x / sqrt 2 - π / 4 * im s)`, display 3.60, and the phase condition
bounds the whole by `r * exp (-0.4798 * |im s|) ≤ sqrt |im s| * exp (-0.4798 * |im s|)`,
which is at most the first coefficient at `σ = 1`.  MEDIUM. -/
theorem leaf_ray_short_sigma_one (δ : ℝ) (s : ℂ) (r : ℝ)
    (hσ1 : s.re = 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) (hspos : 0 < s.im) (hr : 0 < r) (hrs : r ≤ sqrt |s.im|)
    (hexp : 0.4798 * |s.im| + 2 * π * |δ| * r / Real.sqrt 2 ≤ π / 4 * |s.im|) :
    ‖(((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
        (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
          LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t)‖ ≤
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  exact s95_leaf_ray_short_sigma_one δ s r hσ1 ht hsign hspos hr hrs hexp

/-- LEAF: P0014 pages 24 to 25, the case `0 ≤ σ < 1` of the first contour piece,
the integration by parts before display 3.63, display 3.63 itself and the
conclusion after it.  The boundary term is at most `r ^ σ / τ` times the
exponential, the remaining integral at most `(r ^ (σ + 2) + sqrt 2 * r ^ σ) / τ`
times it, and `r ≤ sqrt |im s|`, display 3.61, turns the sum into
`(1 + (1 + sqrt 2) / τ) * τ ^ (σ / 2)`.  HARD. -/
theorem leaf_ray_short_sigma_lt_one (δ : ℝ) (s : ℂ) (r : ℝ)
    (hσ0 : 0 < s.re) (hσ1 : s.re < 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) (hspos : 0 < s.im) (hr : 0 < r) (hrs : r ≤ sqrt |s.im|)
    (hexp : 0.4798 * |s.im| + 2 * π * |δ| * r / Real.sqrt 2 ≤ π / 4 * |s.im|) :
    ‖(((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
        (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
          LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t)‖ ≤
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  sorry

/-- LEAF: the long segment case `sqrt |im s| < r`, outside the paper, whose
segment length obeys display 3.61 of P0014 page 24 and so never reaches this case.
Past the saddle `x = sqrt τ` of the phase `τ log x - x ^ 2 / 2`, an integration by
parts at the far endpoint, as in display 3.63, bounds the extra stretch by
`r ^ (σ - 2) * exp (-0.4798 τ)` up to constants; this leaf records that the parent
leaf as stated needs it.  HARD. -/
theorem leaf_ray_long_segment (δ : ℝ) (s : ℂ) (r : ℝ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) (hspos : 0 < s.im) (hrs : sqrt |s.im| < r)
    (hexp : 0.4798 * |s.im| + 2 * π * |δ| * r / Real.sqrt 2 ≤ π / 4 * |s.im|) :
    ‖(((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
        (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
          LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t)‖ ≤
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  sorry

/-- Assembly of `leaf_initial_segment_ray_bound` from the three leaves, by cases on
`r ≤ sqrt |im s|` and on `s.re = 1`.  Exactly the parent statement. -/
theorem leaf_initial_segment_ray_bound_split (δ : ℝ) (s : ℂ) (r : ℝ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) (hspos : 0 < s.im) (hr : 0 < r)
    (hexp : 0.4798 * |s.im| + 2 * π * |δ| * r / Real.sqrt 2 ≤ π / 4 * |s.im|) :
    ‖(((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
        (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
          LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t)‖ ≤
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  rcases le_or_gt r (sqrt |s.im|) with hrs | hrs
  · rcases eq_or_lt_of_le hσ1 with h1 | h1
    · exact leaf_ray_short_sigma_one δ s r h1 ht hsign hspos hr hrs hexp
    · exact leaf_ray_short_sigma_lt_one δ s r hσ0 h1 ht hsign hspos hr hrs hexp
  · exact leaf_ray_long_segment δ s r hσ0 hσ1 ht hsign hspos hrs hexp

end LeanLab.HelfgottMajor.Decomp511a

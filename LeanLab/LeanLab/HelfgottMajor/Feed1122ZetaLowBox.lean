import LeanLab.PNTPort.StrongPNT.StrongPNT

/-!
# Split of `noLowZero_level_one`: `ζ` has no zero in `(0,1) × (0,1]`, burst 20261122 S126

The conductor one leaf of `Feed1122VeryLowNoZero` asks that the Riemann zeta function have no
zero `ρ` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 1`. Helfgott, arXiv 1305.2897v4 Section 4.6 page 56,
takes it from Platt's verification [Pla11]; at this height no zero computation is needed, the
Euler Maclaurin formula with two Bernoulli terms already separates `ζ` from `0`:

`ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)/2 · ∫_1^∞ B₂({u}) u^(-s-2) du`, valid for `Re s > 0`,
with `B₂(y) = y² - y + 1/6`, Edwards, Riemann's Zeta Function, 1974, Chapter 6, and
Titchmarsh, The Theory of the Riemann Zeta-Function, Section 2.1, display 2.1.5 integrated by
parts once more. The main term is `1/(s-1) + 1/2 + s/12`.

* LEAF `riemannZeta_eq_EM2`: that formula, from the first order formula `ZetaAltFormula` of the
  PNT port by one integration by parts on each `[n, n+1]`. Class MEDIUM.
* PROVED `norm_EM2_int_le`: `|B₂| ≤ 1/6`, so the integral is at most `1/(6(Re s + 1))`.
* PROVED `zeta_lowbox_ineq`: on the box the main term beats the remainder, a polynomial
  inequality in `Re s` and `Im s`, squared: left side below `20`, right side above `36`.
* PROVED `riemannZeta_ne_zero_lowbox`: the assembly.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaLowBox
open Complex Set MeasureTheory

/-- LEAF: Euler Maclaurin formula for `ζ` with two Bernoulli terms, valid in `Re s > 0`, Edwards,
Riemann's Zeta Function, Chapter 6, and Titchmarsh Section 2.1 display 2.1.5 integrated by parts
once more: `ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)/2 ∫_1^∞ B₂({u}) u^(-s-2) du`. In the lab it
follows from `ZetaAltFormula`, `ζ = 1 + 1/(s-1) - s ∫_1^∞ {u} u^(-s-1) du`, by splitting
`{u} = 1/2 + ({u} - 1/2)` and integrating `({u} - 1/2) u^(-s-1)` by parts on each `[n, n+1]`
against `B₂({u})/2`, whose values at the integers are `1/12`. Class MEDIUM. -/
theorem riemannZeta_eq_EM2 {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) / 2 *
      ∫ u in Ioi (1 : ℝ), (((Int.fract u) ^ 2 - Int.fract u + 1 / 6 : ℝ) : ℂ) *
        (u : ℂ) ^ (-s - 2) := by
  sorry

/-- The second Bernoulli polynomial is at most `1/6` in absolute value on `[0, 1)`. -/
lemma abs_bernoulli2_fract_le (x : ℝ) :
    |(Int.fract x) ^ 2 - Int.fract x + 1 / 6| ≤ 1 / 6 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [abs_le]
  constructor <;> nlinarith

/-- The remainder integral of the second order formula is at most `1/(6(Re s + 1))`, the
argument of `norm_zetaInt_le` in `PNTPort.ZetaZeros.SmallT` with `|B₂| ≤ 1/6`. -/
lemma norm_EM2_int_le {s : ℂ} (hs : -1 < s.re) :
    ‖∫ u in Ioi (1 : ℝ), (((Int.fract u) ^ 2 - Int.fract u + 1 / 6 : ℝ) : ℂ) *
      (u : ℂ) ^ (-s - 2)‖ ≤ 1 / (6 * (s.re + 1)) := by
  have domBound {x : ℝ} (hu : x ∈ Ioi 1) :
      |(Int.fract x) ^ 2 - Int.fract x + 1 / 6| * ‖(x : ℂ) ^ (-s - 2)‖
        ≤ 1 / 6 * x ^ (-s.re - 2) := by
    rw [mem_Ioi] at hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [sub_re, neg_re, ofReal_ofNat, re_ofNat]
    exact mul_le_mul_of_nonneg_right (abs_bernoulli2_fract_le x)
      (Real.rpow_nonneg (by linarith) _)
  have domIntegral : Integrable (fun x : ℝ => 1 / 6 * x ^ (-s.re - 2))
      (volume.restrict (Set.Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hI := integral_Ioi_rpow_of_lt (a := -s.re - 2) (by linarith) one_pos
  have hval : ∫ x in Ioi (1 : ℝ), 1 / 6 * x ^ (-s.re - 2) = 1 / (6 * (s.re + 1)) := by
    rw [integral_const_mul, hI, Real.one_rpow]
    have : -s.re - 2 + 1 = -(s.re + 1) := by ring
    rw [this]
    have hp : s.re + 1 ≠ 0 := by linarith
    field_simp
  rw [← hval]
  refine integral_mono_ae ?_ domIntegral ?_
  · refine domIntegral.mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.comp
        (((measurable_fract.pow_const 2).sub measurable_fract).add_const _)).mul
        (Complex.measurable_ofReal.pow_const _)).norm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact domBound hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact domBound hx

/-- On the box `0 < Re s < 1`, `0 < Im s ≤ 1` the main term of the second order formula beats
the remainder bound. Squared: `|s|² |s+1|² |s-1|² < 2 · 5 · 2 = 20` and
`(Re s + 1)² |s+2|² |s+3|² > 1 · 4 · 9 = 36`. -/
lemma zeta_lowbox_ineq (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 0 < s.im)
    (ht1 : s.im ≤ 1) :
    ‖s‖ * ‖s + 1‖ / (12 * (s.re + 1)) < ‖(s + 2) * (s + 3) / (12 * (s - 1))‖ := by
  set σ := s.re
  set t := s.im
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have a1 : ‖s‖ ^ 2 < 2 := by rw [hsq]; nlinarith
  have a2 : ‖s + 1‖ ^ 2 < 5 := by
    rw [hsq]; simp only [add_re, one_re, add_im, one_im]; nlinarith
  have a3 : ‖s - 1‖ ^ 2 < 2 := by
    rw [hsq]; simp only [sub_re, one_re, sub_im, one_im]; nlinarith
  have b2 : 4 < ‖s + 2‖ ^ 2 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have b3 : 9 < ‖s + 3‖ ^ 2 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have hn1 : 0 < ‖s - 1‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hA : 0 ≤ ‖s‖ * ‖s + 1‖ * ‖s - 1‖ := by positivity
  have hkey : ‖s‖ * ‖s + 1‖ * ‖s - 1‖ < (σ + 1) * (‖s + 2‖ * ‖s + 3‖) := by
    have hB : 0 ≤ (σ + 1) * (‖s + 2‖ * ‖s + 3‖) := by positivity
    have lhs : (‖s‖ * ‖s + 1‖ * ‖s - 1‖) ^ 2 < 20 := by
      have e : (‖s‖ * ‖s + 1‖ * ‖s - 1‖) ^ 2 = ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s - 1‖ ^ 2 := by ring
      rw [e]
      have p1 : 0 ≤ ‖s‖ ^ 2 := by positivity
      have p2 : 0 ≤ ‖s + 1‖ ^ 2 := by positivity
      have p3 : 0 ≤ ‖s - 1‖ ^ 2 := by positivity
      have q1 : ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 < 2 * 5 := mul_lt_mul'' a1 a2 p1 p2
      have q2 := mul_lt_mul'' q1 a3 (by positivity) p3
      linarith
    have rhs : 36 < ((σ + 1) * (‖s + 2‖ * ‖s + 3‖)) ^ 2 := by
      have e : ((σ + 1) * (‖s + 2‖ * ‖s + 3‖)) ^ 2 =
          (σ + 1) ^ 2 * (‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2) := by ring
      rw [e]
      have c1 : 1 < (σ + 1) ^ 2 := by nlinarith
      have c2 : 36 < ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 := by nlinarith
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hB (by linarith)
  rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `ζ` has no zero `ρ` with `0 < Re ρ < 1` and `0 < Im ρ ≤ 1`: the second order Euler Maclaurin
formula, the remainder bound, and the box inequality. -/
theorem riemannZeta_ne_zero_lowbox (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (ht0 : 0 < ρ.im)
    (ht1 : ρ.im ≤ 1) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hEM := riemannZeta_eq_EM2 h0 hρ1
  set I := ∫ u in Ioi (1 : ℝ), (((Int.fract u) ^ 2 - Int.fract u + 1 / 6 : ℝ) : ℂ) *
    (u : ℂ) ^ (-ρ - 2) with hI
  have hmain : (ρ + 2) * (ρ + 3) / (12 * (ρ - 1)) = ρ * (ρ + 1) / 2 * I := by
    rw [hz] at hEM
    linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / (6 * (ρ.re + 1)) := norm_EM2_int_le (by linarith)
  have hlt := zeta_lowbox_ineq ρ h0 h1 ht0 ht1
  rw [hmain, norm_mul, norm_div, norm_mul, Complex.norm_ofNat] at hlt
  have hpos : 0 ≤ ‖ρ‖ * ‖ρ + 1‖ / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hIle hpos
  have e : ‖ρ‖ * ‖ρ + 1‖ / 2 * (1 / (6 * (ρ.re + 1))) = ‖ρ‖ * ‖ρ + 1‖ / (12 * (ρ.re + 1)) := by
    field_simp
    ring
  linarith

end LeanLab.HelfgottMajor.Feed1122ZetaLowBox

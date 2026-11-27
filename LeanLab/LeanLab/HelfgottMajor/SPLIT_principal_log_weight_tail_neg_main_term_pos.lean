import Mathlib

/-!
Split of the leaf `Decomp457b.tail_neg_digamma_main_term_envelope`, the elementary envelope
closing the gamma factor step of P0014, Helfgott, Major arcs for Goldbach's problem,
arXiv 1305.2897, page 34 display 4.10, on the line of real part minus one half.

The main term at height `-t` is the complex conjugate of the main term at height `t`, so its
norm is even in `t`; this symmetry is proved here. The positive range `2 ≤ t` is then split
at `t = 5/2`: numerically the margin of the envelope is `0.00040` at `t = 2`, already `0.226`
at `t = 5/2`, `0.383` at `t = 3` and increasing to about `1.37` by `t = 10^4`.
AI wrote this Lean code. Binary Goldbach is open.
-/

set_option linter.unusedSimpArgs false

namespace LeanLab.HelfgottMajor.Decomp457b
namespace TailNegMainTerm
open Complex ComplexConjugate

/-- LEAF: the elementary envelope of P0014 page 34 display 4.10 on the line of real part
minus one half, near range `2 ≤ t ≤ 5/2`: the explicit Stirling main term at `w = 5/2 + it`
minus the three recurrence terms, plus the remainder budget `2/9375`, is at most
`log t + 3/2`. Numerically the margin is `0.00040` at `t = 2` and `0.226` at `t = 5/2`, so
the argument of `w` and the logarithm need about four correct digits near `t = 2`.
Class HARD: a sharp real variable inequality on a compact range, rigorous numerics. -/
theorem main_term_envelope_near (t : ℝ) (ht : 2 ≤ t) (ht' : t ≤ 5 / 2) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log t + 3 / 2 := by
  sorry

/-- LEAF: the elementary envelope of P0014 page 34 display 4.10 on the line of real part
minus one half, far range `5/2 ≤ t`: the explicit Stirling main term at `w = 5/2 + it` minus
the three recurrence terms, plus `2/9375`, is at most `log t + 3/2`. Here the margin is at
least `0.226`. A route: `‖log w‖^2 = (log |w|)^2 + (arg w)^2` with `0 < arg w < π/2` and
`log |w| ≤ log t + 25/(8 t^2)`, so `‖log w‖ ≤ log |w| + (π/2)^2/(2 log |w|)`, and the other
five reciprocal terms are bounded by their moduli, about `3/t` for the recurrence terms.
Class MEDIUM: an elementary real inequality on an unbounded range. -/
theorem main_term_envelope_far (t : ℝ) (ht : 5 / 2 ≤ t) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log t + 3 / 2 := by
  have h₀ : t > 0 := by linarith
  have h₁ : (5 / 2 : ℝ) > 0 := by norm_num
  -- Define w = 5/2 + t*I
  have h_w_def : (5 / 2 : ℂ) + t * I = (5 / 2 : ℂ) + t * I := rfl
  -- Step 1: Bound the norm of log(w)
  have h_log_w_norm_sq : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ ^ 2 = (Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 + ((5 / 2 : ℂ) + t * I).arg ^ 2 := by
  have h₁ : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ ^ 2 = (Complex.log ((5 / 2 : ℂ) + t * I)).re ^ 2 + (Complex.log ((5 / 2 : ℂ) + t * I)).im ^ 2 := by
    simp [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply]
    <;> ring_nf
    <;> simp [Complex.ext_iff, pow_two]
    <;> ring_nf
  rw [h₁]
  have h₂ : (Complex.log ((5 / 2 : ℂ) + t * I)).re = Real.log ‖(5 / 2 : ℂ) + t * I‖ := by
    rw [Complex.log_re]
  have h₃ : (Complex.log ((5 / 2 : ℂ) + t * I)).im = ((5 / 2 : ℂ) + t * I).arg := by
    rw [Complex.log_im]
  rw [h₂, h₃]
  <;> ring_nf
  have h_arg_w_pos : 0 < ((5 / 2 : ℂ) + t * I).arg := by
  have h₁ : 0 < ((5 / 2 : ℂ) + t * I).arg := by
    -- The argument of a complex number with positive real and imaginary parts is positive
    have h₂ : 0 < (5 / 2 : ℝ) := by norm_num
    have h₃ : 0 < t := by linarith
    have h₄ : 0 < (t : ℝ) := by exact_mod_cast h₃
    -- Use the fact that arg(z) = arctan(im(z)/re(z)) for re(z) > 0
    have h₅ : ((5 / 2 : ℂ) + t * I).arg = Real.arctan (t / (5 / 2 : ℝ)) := by
      rw [Complex.arg_re_pos (by norm_num : (0 : ℝ) < 5 / 2)]
      <;> simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
      <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num
      <;> simp_all [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
      <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num <;> linarith
    rw [h₅]
    -- arctan(x) > 0 for x > 0
    apply Real.arctan_pos.mpr
    positivity
  exact h₁
  have h_arg_w_lt_pi_div_two : ((5 / 2 : ℂ) + t * I).arg < Real.pi / 2 := by
  have h₁ : ((5 / 2 : ℂ) + t * I).arg < Real.pi / 2 := by
    have h₂ : 0 < (5 / 2 : ℝ) := by norm_num
    have h₃ : 0 < t := by linarith
    have h₄ : ((5 / 2 : ℂ) + t * I).arg = Real.arctan (t / (5 / 2 : ℝ)) := by
      rw [Complex.arg_re_pos (by norm_num : (0 : ℝ) < 5 / 2)]
      <;> simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
      <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num
      <;> simp_all [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
      <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num <;> linarith
    rw [h₄]
    -- arctan(x) < π/2 for all x
    have h₅ : Real.arctan (t / (5 / 2 : ℝ)) < Real.pi / 2 := by
      linarith [Real.arctan_lt_pi_div_two (t / (5 / 2 : ℝ))]
    exact h₅
  exact h₁
  have h_log_abs_w_le : Real.log ‖(5 / 2 : ℂ) + t * I‖ ≤ Real.log t + 25 / (8 * t ^ 2) := by
  have h₁ : ‖(5 / 2 : ℂ) + t * I‖ = Real.sqrt (t ^ 2 + (5 / 2 : ℝ) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq_apply, Complex.ext_iff, pow_two]
    <;> ring_nf
    <;> field_simp [Real.sqrt_eq_iff_sq_eq]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  rw [h₁]
  have h₂ : Real.log (Real.sqrt (t ^ 2 + (5 / 2 : ℝ) ^ 2)) = Real.log (Real.sqrt (t ^ 2 + 25 / 4)) := by
    norm_num
    <;> ring_nf
  rw [h₂]
  have h₃ : Real.log (Real.sqrt (t ^ 2 + 25 / 4)) = Real.log (t * Real.sqrt (1 + 25 / (4 * t ^ 2))) := by
    have h₄ : 0 < t := by linarith
    have h₅ : 0 < (t : ℝ) := by positivity
    have h₆ : Real.sqrt (t ^ 2 + 25 / 4) = t * Real.sqrt (1 + 25 / (4 * t ^ 2)) := by
      have h₇ : Real.sqrt (t ^ 2 + 25 / 4) = Real.sqrt (t ^ 2 * (1 + 25 / (4 * t ^ 2))) := by
        have h₈ : (t : ℝ) ≠ 0 := by linarith
        field_simp [h₈]
        <;> ring_nf
        <;> field_simp [h₈]
        <;> ring_nf
      rw [h₇]
      have h₉ : Real.sqrt (t ^ 2 * (1 + 25 / (4 * t ^ 2))) = t * Real.sqrt (1 + 25 / (4 * t ^ 2)) := by
        rw [Real.sqrt_mul (by positivity)]
        <;> field_simp [Real.sqrt_sq_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t)]
        <;> ring_nf
      rw [h₉]
    rw [h₆]
    <;> simp [Real.log_mul, Real.log_sqrt, Real.log_rpow, Real.log_pow]
    <;> field_simp [Real.log_mul, Real.log_sqrt, Real.log_rpow, Real.log_pow]
    <;> ring_nf
    <;> field_simp [Real.log_mul, Real.log_sqrt, Real.log_rpow, Real.log_pow]
    <;> linarith
  rw [h₃]
  have h₄ : Real.log (t * Real.sqrt (1 + 25 / (4 * t ^ 2))) = Real.log t + Real.log (Real.sqrt (1 + 25 / (4 * t ^ 2))) := by
    have h₅ : 0 < t := by linarith
    have h₆ : 0 < Real.sqrt (1 + 25 / (4 * t ^ 2)) := by positivity
    have h₇ : 0 < t * Real.sqrt (1 + 25 / (4 * t ^ 2)) := by positivity
    rw [Real.log_mul (by positivity) (by positivity)]
  rw [h₄]
  have h₅ : Real.log (Real.sqrt (1 + 25 / (4 * t ^ 2))) = 1 / 2 * Real.log (1 + 25 / (4 * t ^ 2)) := by
    have h₆ : 0 < (1 + 25 / (4 * t ^ 2) : ℝ) := by positivity
    have h₇ : Real.log (Real.sqrt (1 + 25 / (4 * t ^ 2))) = 1 / 2 * Real.log (1 + 25 / (4 * t ^ 2)) := by
      rw [Real.log_sqrt (by positivity)]
      <;> ring_nf
    rw [h₇]
  rw [h₅]
  have h₆ : Real.log (1 + 25 / (4 * t ^ 2)) ≤ 25 / (4 * t ^ 2) := by
    have h₇ : 0 < (25 / (4 * t ^ 2) : ℝ) := by positivity
    have h₈ : Real.log (1 + 25 / (4 * t ^ 2)) ≤ 25 / (4 * t ^ 2) := by
      have h₉ : Real.log (1 + 25 / (4 * t ^ 2)) ≤ 25 / (4 * t ^ 2) := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 25 / (4 * t ^ 2))]
      linarith
    linarith
  have h₇ : 1 / 2 * Real.log (1 + 25 / (4 * t ^ 2)) ≤ 1 / 2 * (25 / (4 * t ^ 2)) := by
    gcongr
  have h₈ : 1 / 2 * (25 / (4 * t ^ 2)) = 25 / (8 * t ^ 2) := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  linarith
  have h_log_abs_w_pos : 0 < Real.log ‖(5 / 2 : ℂ) + t * I‖ := by
  have h₁ : ‖(5 / 2 : ℂ) + t * I‖ > 1 := by
    have h₂ : ‖(5 / 2 : ℂ) + t * I‖ ^ 2 = (5 / 2 : ℝ) ^ 2 + t ^ 2 := by
      simp [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> nlinarith
    have h₃ : (5 / 2 : ℝ) ^ 2 + t ^ 2 > 1 := by
      have h₄ : t ≥ 5 / 2 := ht
      nlinarith
    have h₄ : ‖(5 / 2 : ℂ) + t * I‖ > 0 := by positivity
    nlinarith [sq_nonneg (‖(5 / 2 : ℂ) + t * I‖ - 1), sq_nonneg (‖(5 / 2 : ℂ) + t * I‖ + 1)]
  have h₂ : Real.log ‖(5 / 2 : ℂ) + t * I‖ > Real.log 1 := by
    apply Real.log_lt_log (by positivity) h₁
  have h₃ : Real.log 1 = (0 : ℝ) := by norm_num
  linarith
  have h_log_w_norm_le : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ ≤ Real.log ‖(5 / 2 : ℂ) + t * I‖ + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) := by
  have h₁ : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ ^ 2 = (Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 + ((5 / 2 : ℂ) + t * I).arg ^ 2 := h_log_w_norm_sq
  have h₂ : 0 ≤ Real.log ‖(5 / 2 : ℂ) + t * I‖ := by linarith [h_log_abs_w_pos]
  have h₃ : 0 < Real.log ‖(5 / 2 : ℂ) + t * I‖ := h_log_abs_w_pos
  have h₄ : 0 ≤ ((5 / 2 : ℂ) + t * I).arg := by linarith [h_arg_w_pos]
  have h₅ : ((5 / 2 : ℂ) + t * I).arg < Real.pi / 2 := h_arg_w_lt_pi_div_two
  have h₆ : 0 ≤ (Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 := by positivity
  have h₇ : 0 ≤ ((5 / 2 : ℂ) + t * I).arg ^ 2 := by positivity
  -- Use the inequality sqrt(a² + b²) ≤ a + b²/(2a) for a > 0
  have h₈ : Real.sqrt ((Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 + ((5 / 2 : ℂ) + t * I).arg ^ 2) ≤ Real.log ‖(5 / 2 : ℂ) + t * I‖ + ((5 / 2 : ℂ) + t * I).arg ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) := by
    have h₉ : 0 < Real.log ‖(5 / 2 : ℂ) + t * I‖ := h_log_abs_w_pos
    have h₁₀ : 0 ≤ ((5 / 2 : ℂ) + t * I).arg ^ 2 := by positivity
    have h₁₁ : 0 ≤ (Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 := by positivity
    -- Prove that (a + b²/(2a))² ≥ a² + b²
    have h₁₂ : (Real.log ‖(5 / 2 : ℂ) + t * I‖ + ((5 / 2 : ℂ) + t * I).arg ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖)) ^ 2 ≥ (Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 + ((5 / 2 : ℂ) + t * I).arg ^ 2 := by
      have h₁₃ : 0 < Real.log ‖(5 / 2 : ℂ) + t * I‖ := h_log_abs_w_pos
      have h₁₄ : 0 < 2 * Real.log ‖(5 / 2 : ℂ) + t * I‖ := by positivity
      field_simp [h₁₃.ne', h₁₄.ne']
      rw [le_div_iff (by positivity)]
      nlinarith [sq_nonneg (((5 / 2 : ℂ) + t * I).arg ^ 2), sq_nonneg (Real.log ‖(5 / 2 : ℂ) + t * I‖ ^ 2),
        sq_nonneg (Real.log ‖(5 / 2 : ℂ) + t * I‖ ^ 2 - ((5 / 2 : ℂ) + t * I).arg ^ 2)]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have h₉ : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ = Real.sqrt ((Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 + ((5 / 2 : ℂ) + t * I).arg ^ 2) := by
    have h₁₀ : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ ≥ 0 := by positivity
    have h₁₁ : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ ^ 2 = (Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 + ((5 / 2 : ℂ) + t * I).arg ^ 2 := h_log_w_norm_sq
    have h₁₂ : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ = Real.sqrt ((Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 + ((5 / 2 : ℂ) + t * I).arg ^ 2) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg _, Real.sq_sqrt (by positivity : 0 ≤ (Real.log ‖(5 / 2 : ℂ) + t * I‖) ^ 2 + ((5 / 2 : ℂ) + t * I).arg ^ 2)]
    exact h₁₂
  rw [h₉]
  have h₁₀ : Real.log ‖(5 / 2 : ℂ) + t * I‖ + ((5 / 2 : ℂ) + t * I).arg ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) ≤ Real.log ‖(5 / 2 : ℂ) + t * I‖ + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) := by
    have h₁₁ : ((5 / 2 : ℂ) + t * I).arg ^ 2 ≤ (Real.pi / 2) ^ 2 := by
      have h₁₂ : ((5 / 2 : ℂ) + t * I).arg < Real.pi / 2 := h_arg_w_lt_pi_div_two
      have h₁₃ : 0 ≤ ((5 / 2 : ℂ) + t * I).arg := by linarith [h_arg_w_pos]
      have h₁₄ : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have h₁₂ : 0 < Real.log ‖(5 / 2 : ℂ) + t * I‖ := h_log_abs_w_pos
    have h₁₃ : 0 < 2 * Real.log ‖(5 / 2 : ℂ) + t * I‖ := by positivity
    have h₁₄ : ((5 / 2 : ℂ) + t * I).arg ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) ≤ (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) := by
      apply div_le_div_of_le_of_nonneg h₁₁ (by positivity)
    linarith
  linarith
  -- Step 2: Bound the reciprocal terms
  have h_inv_2w_norm : ‖(1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))‖ ≤ 1 / (2 * t) := by
  have h₁ : ‖(1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))‖ = 1 / (2 * ‖(5 / 2 : ℂ) + t * I‖) := by
    calc
      ‖(1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))‖ = ‖(1 : ℂ)‖ / ‖(2 : ℂ) * ((5 / 2 : ℂ) + t * I)‖ := by
        simp [Complex.norm_div]
      _ = 1 / ‖(2 : ℂ) * ((5 / 2 : ℂ) + t * I)‖ := by simp [Complex.norm_one]
      _ = 1 / (‖(2 : ℂ)‖ * ‖(5 / 2 : ℂ) + t * I‖) := by
        rw [Complex.norm_mul]
      _ = 1 / (2 * ‖(5 / 2 : ℂ) + t * I‖) := by
        norm_num [Complex.norm_eq_abs, Complex.abs_ofReal]
        <;> field_simp [Real.norm_eq_abs]
        <;> ring_nf
        <;> norm_num
  rw [h₁]
  have h₂ : ‖(5 / 2 : ℂ) + t * I‖ ≥ t := by
    have h₃ : ‖(5 / 2 : ℂ) + t * I‖ ^ 2 = (5 / 2 : ℝ) ^ 2 + t ^ 2 := by
      simp [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> nlinarith
    have h₄ : (‖(5 / 2 : ℂ) + t * I‖ : ℝ) ≥ 0 := by positivity
    have h₅ : (t : ℝ) ≥ 0 := by positivity
    nlinarith [sq_nonneg (‖(5 / 2 : ℂ) + t * I‖ - t), sq_nonneg (‖(5 / 2 : ℂ) + t * I‖ + t)]
  have h₃ : (1 : ℝ) / (2 * ‖(5 / 2 : ℂ) + t * I‖) ≤ 1 / (2 * t) := by
    have h₄ : 0 < (t : ℝ) := by positivity
    have h₅ : 0 < ‖(5 / 2 : ℂ) + t * I‖ := by positivity
    have h₆ : 0 < 2 * ‖(5 / 2 : ℂ) + t * I‖ := by positivity
    have h₇ : 0 < 2 * t := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  linarith
  have h_inv_12w2_norm : ‖(1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)‖ ≤ 1 / (12 * t ^ 2) := by
  have h₁ : ‖(1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)‖ = 1 / (12 * ‖(5 / 2 : ℂ) + t * I‖ ^ 2) := by
    calc
      ‖(1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)‖ = ‖(1 : ℂ)‖ / ‖(12 : ℂ) * ((5 / 2 : ℂ) + t * I) ^ 2‖ := by
        simp [Complex.norm_div]
      _ = 1 / ‖(12 : ℂ) * ((5 / 2 : ℂ) + t * I) ^ 2‖ := by simp [Complex.norm_one]
      _ = 1 / (‖(12 : ℂ)‖ * ‖((5 / 2 : ℂ) + t * I) ^ 2‖) := by
        rw [Complex.norm_mul]
      _ = 1 / (‖(12 : ℂ)‖ * ‖(5 / 2 : ℂ) + t * I‖ ^ 2) := by
        rw [Complex.norm_pow]
        <;> norm_num
      _ = 1 / (12 * ‖(5 / 2 : ℂ) + t * I‖ ^ 2) := by
        norm_num [Complex.norm_eq_abs, Complex.abs_ofReal]
        <;> field_simp [Real.norm_eq_abs]
        <;> ring_nf
        <;> norm_num
  rw [h₁]
  have h₂ : ‖(5 / 2 : ℂ) + t * I‖ ^ 2 ≥ t ^ 2 := by
    have h₃ : ‖(5 / 2 : ℂ) + t * I‖ ^ 2 = (5 / 2 : ℝ) ^ 2 + t ^ 2 := by
      simp [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> nlinarith
    rw [h₃]
    <;> nlinarith
  have h₃ : (1 : ℝ) / (12 * ‖(5 / 2 : ℂ) + t * I‖ ^ 2) ≤ 1 / (12 * t ^ 2) := by
    have h₄ : 0 < (t : ℝ) := by positivity
    have h₅ : 0 < (t : ℝ) ^ 2 := by positivity
    have h₆ : 0 < ‖(5 / 2 : ℂ) + t * I‖ ^ 2 := by positivity
    have h₇ : 0 < 12 * ‖(5 / 2 : ℂ) + t * I‖ ^ 2 := by positivity
    have h₈ : 0 < 12 * (t : ℝ) ^ 2 := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  linarith
  have h_inv_neg_half_it_norm : ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ ≤ 1 / t := by
  have h₁ : ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ = 1 / ‖(-1 / 2 : ℂ) + t * I‖ := by
    rw [Complex.norm_inv]
    <;> field_simp
  rw [h₁]
  have h₂ : ‖(-1 / 2 : ℂ) + t * I‖ ≥ t := by
    have h₃ : ‖(-1 / 2 : ℂ) + t * I‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
      simp [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> nlinarith
    have h₄ : (‖(-1 / 2 : ℂ) + t * I‖ : ℝ) ≥ 0 := by positivity
    have h₅ : (t : ℝ) ≥ 0 := by positivity
    nlinarith [sq_nonneg (‖(-1 / 2 : ℂ) + t * I‖ - t), sq_nonneg (‖(-1 / 2 : ℂ) + t * I‖ + t)]
  have h₃ : (1 : ℝ) / ‖(-1 / 2 : ℂ) + t * I‖ ≤ 1 / t := by
    have h₄ : 0 < (t : ℝ) := by positivity
    have h₅ : 0 < ‖(-1 / 2 : ℂ) + t * I‖ := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  linarith
  have h_inv_half_it_norm : ‖((1 / 2 : ℂ) + t * I)⁻¹‖ ≤ 1 / t := by
  have h₁ : ‖((1 / 2 : ℂ) + t * I)⁻¹‖ = 1 / ‖(1 / 2 : ℂ) + t * I‖ := by
    rw [Complex.norm_inv]
    <;> field_simp
  rw [h₁]
  have h₂ : ‖(1 / 2 : ℂ) + t * I‖ ≥ t := by
    have h₃ : ‖(1 / 2 : ℂ) + t * I‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
      simp [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> nlinarith
    have h₄ : (‖(1 / 2 : ℂ) + t * I‖ : ℝ) ≥ 0 := by positivity
    have h₅ : (t : ℝ) ≥ 0 := by positivity
    nlinarith [sq_nonneg (‖(1 / 2 : ℂ) + t * I‖ - t), sq_nonneg (‖(1 / 2 : ℂ) + t * I‖ + t)]
  have h₃ : (1 : ℝ) / ‖(1 / 2 : ℂ) + t * I‖ ≤ 1 / t := by
    have h₄ : 0 < (t : ℝ) := by positivity
    have h₅ : 0 < ‖(1 / 2 : ℂ) + t * I‖ := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  linarith
  have h_inv_three_half_it_norm : ‖((3 / 2 : ℂ) + t * I)⁻¹‖ ≤ 1 / t := by
  have h₁ : ‖((3 / 2 : ℂ) + t * I)⁻¹‖ = 1 / ‖(3 / 2 : ℂ) + t * I‖ := by
    rw [Complex.norm_inv]
    <;> field_simp
  rw [h₁]
  have h₂ : ‖(3 / 2 : ℂ) + t * I‖ ≥ t := by
    have h₃ : ‖(3 / 2 : ℂ) + t * I‖ ^ 2 = (3 / 2 : ℝ) ^ 2 + t ^ 2 := by
      simp [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply, Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> nlinarith
    have h₄ : (‖(3 / 2 : ℂ) + t * I‖ : ℝ) ≥ 0 := by positivity
    have h₅ : (t : ℝ) ≥ 0 := by positivity
    nlinarith [sq_nonneg (‖(3 / 2 : ℂ) + t * I‖ - t), sq_nonneg (‖(3 / 2 : ℂ) + t * I‖ + t)]
  have h₃ : (1 : ℝ) / ‖(3 / 2 : ℂ) + t * I‖ ≤ 1 / t := by
    have h₄ : 0 < (t : ℝ) := by positivity
    have h₅ : 0 < ‖(3 / 2 : ℂ) + t * I‖ := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith
  linarith
  -- Step 3: Combine using triangle inequality
  have h_main_ineq : ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
      1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
    (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ ≤
    Real.log t + 25 / (8 * t ^ 2) + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) +
    1 / (2 * t) + 1 / (12 * t ^ 2) + 3 / t := by
  have h₁ : ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
      1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
    (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ ≤
    ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ + ‖(1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))‖ +
    ‖(1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)‖ + ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ +
    ‖((1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((3 / 2 : ℂ) + t * I)⁻¹‖ := by
    calc
      ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ =
          ‖Complex.log ((5 / 2 : ℂ) + t * I) + (-(1 / (2 * ((5 / 2 : ℂ) + t * I)))) +
            (-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2))) +
            (-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ := by
        ring_nf
        <;> simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
        <;> norm_num
        <;> simp_all [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
        <;> ring_nf at *
        <;> norm_num at *
        <;> linarith
      _ ≤ ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ + ‖(-(1 / (2 * ((5 / 2 : ℂ) + t * I))))‖ +
          ‖(-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)))‖ +
          ‖(-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ := by
        -- Triangle inequality for multiple terms
        calc
          ‖Complex.log ((5 / 2 : ℂ) + t * I) + (-(1 / (2 * ((5 / 2 : ℂ) + t * I)))) +
              (-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2))) +
              (-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ ≤
            ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ + ‖(-(1 / (2 * ((5 / 2 : ℂ) + t * I))))‖ +
              ‖(-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)))‖ +
              ‖(-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ := by
            -- Apply triangle inequality multiple times
            calc
              ‖Complex.log ((5 / 2 : ℂ) + t * I) + (-(1 / (2 * ((5 / 2 : ℂ) + t * I)))) +
                  (-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2))) +
                  (-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ =
                ‖Complex.log ((5 / 2 : ℂ) + t * I) + (-(1 / (2 * ((5 / 2 : ℂ) + t * I)))) +
                  (-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2))) +
                  (-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ := by rfl
              _ ≤ ‖Complex.log ((5 / 2 : ℂ) + t * I) + (-(1 / (2 * ((5 / 2 : ℂ) + t * I)))) +
                  (-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2))))‖ +
                ‖(-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ := by
                apply norm_add_le
              _ ≤ ‖Complex.log ((5 / 2 : ℂ) + t * I) + (-(1 / (2 * ((5 / 2 : ℂ) + t * I))))‖ +
                ‖(-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)))‖ +
                ‖(-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ := by
                apply add_le_add_right (norm_add_le _ _)
              _ ≤ ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ + ‖(-(1 / (2 * ((5 / 2 : ℂ) + t * I))))‖ +
                ‖(-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)))‖ +
                ‖(-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ := by
                apply add_le_add_right (add_le_add_right (norm_add_le _ _))
          _ = ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ + ‖(-(1 / (2 * ((5 / 2 : ℂ) + t * I))))‖ +
            ‖(-(1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)))‖ +
            ‖(-(((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹))‖ := by rfl
      _ = ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ + ‖(1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))‖ +
          ‖(1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)‖ +
          ‖((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹‖ := by
        simp [norm_neg, norm_neg, norm_neg]
        <;> ring_nf
        <;> simp [norm_add_le]
      _ ≤ ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ + ‖(1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))‖ +
          ‖(1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)‖ + ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ +
          ‖((1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((3 / 2 : ℂ) + t * I)⁻¹‖ := by
        have h₂ : ‖((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹‖ ≤
            ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((3 / 2 : ℂ) + t * I)⁻¹‖ := by
          calc
            ‖((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹‖ ≤
              ‖((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((3 / 2 : ℂ) + t * I)⁻¹‖ := by
              apply norm_add_le
            _ ≤ ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((3 / 2 : ℂ) + t * I)⁻¹‖ := by
              have h₃ : ‖((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹‖ ≤ ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((1 / 2 : ℂ) + t * I)⁻¹‖ := by
                apply norm_add_le
              linarith
        linarith
  have h₂ : ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ ≤ Real.log ‖(5 / 2 : ℂ) + t * I‖ + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) := h_log_w_norm_le
  have h₃ : Real.log ‖(5 / 2 : ℂ) + t * I‖ ≤ Real.log t + 25 / (8 * t ^ 2) := h_log_abs_w_le
  have h₄ : ‖(1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))‖ ≤ 1 / (2 * t) := h_inv_2w_norm
  have h₅ : ‖(1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)‖ ≤ 1 / (12 * t ^ 2) := h_inv_12w2_norm
  have h₆ : ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ ≤ 1 / t := h_inv_neg_half_it_norm
  have h₇ : ‖((1 / 2 : ℂ) + t * I)⁻¹‖ ≤ 1 / t := h_inv_half_it_norm
  have h₈ : ‖((3 / 2 : ℂ) + t * I)⁻¹‖ ≤ 1 / t := h_inv_three_half_it_norm
  calc
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
        1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
      (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ ≤
      ‖Complex.log ((5 / 2 : ℂ) + t * I)‖ + ‖(1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))‖ +
      ‖(1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)‖ + ‖((-1 / 2 : ℂ) + t * I)⁻¹‖ +
      ‖((1 / 2 : ℂ) + t * I)⁻¹‖ + ‖((3 / 2 : ℂ) + t * I)⁻¹‖ := h₁
    _ ≤ (Real.log ‖(5 / 2 : ℂ) + t * I‖ + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖)) +
      (1 / (2 * t)) + (1 / (12 * t ^ 2)) + (1 / t) + (1 / t) + (1 / t) := by
      gcongr <;> assumption
    _ = Real.log ‖(5 / 2 : ℂ) + t * I‖ + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) +
      1 / (2 * t) + 1 / (12 * t ^ 2) + 3 / t := by ring
    _ ≤ (Real.log t + 25 / (8 * t ^ 2)) + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) +
      1 / (2 * t) + 1 / (12 * t ^ 2) + 3 / t := by
      gcongr <;> assumption
    _ = Real.log t + 25 / (8 * t ^ 2) + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) +
      1 / (2 * t) + 1 / (12 * t ^ 2) + 3 / t := by ring
  -- Step 4: Final numeric bound
  have h_final : Real.log t + 25 / (8 * t ^ 2) + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) +
    1 / (2 * t) + 1 / (12 * t ^ 2) + 3 / t + 2 / 9375 ≤ Real.log t + 3 / 2 := by
  have h₁ : 25 / (8 * t ^ 2) + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) +
      1 / (2 * t) + 1 / (12 * t ^ 2) + 3 / t + 2 / 9375 ≤ 3 / 2 := by sorry
  linarith
  -- Combine all steps
  have h₂ : ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
      1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
    (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
    2 / 9375 ≤ Real.log t + 3 / 2 := by
  have h₃ : ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
      1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
    (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ ≤
    Real.log t + 25 / (8 * t ^ 2) + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) +
    1 / (2 * t) + 1 / (12 * t ^ 2) + 3 / t := h_main_ineq
  have h₄ : Real.log t + 25 / (8 * t ^ 2) + (Real.pi / 2) ^ 2 / (2 * Real.log ‖(5 / 2 : ℂ) + t * I‖) +
    1 / (2 * t) + 1 / (12 * t ^ 2) + 3 / t + 2 / 9375 ≤ Real.log t + 3 / 2 := h_final
  linarith
  exact h₂

/-- The norm of the main term is even in `t`: at `-t` every quantity is the complex
conjugate of the one at `t`, and `log` commutes with conjugation off the negative axis. -/
theorem main_term_norm_neg (t : ℝ) :
    ‖Complex.log ((5 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) -
          1 / (2 * ((5 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)) -
          1 / (12 * ((5 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) ^ 2) -
        (((-1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)⁻¹ + ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)⁻¹ +
          ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)⁻¹)‖ =
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ := by
  have harg : ((5 / 2 : ℂ) + t * I).arg ≠ Real.pi := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    norm_num at this
  have e1 : (5 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((5 / 2 : ℂ) + t * I) := by
    simp only [map_add, map_mul, map_div₀, map_neg, map_one, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I]; push_cast; ring
  have e2 : (-1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((-1 / 2 : ℂ) + t * I) := by
    simp only [map_add, map_mul, map_div₀, map_neg, map_one, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I]; push_cast; ring
  have e3 : (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((1 / 2 : ℂ) + t * I) := by
    simp only [map_add, map_mul, map_div₀, map_neg, map_one, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I]; push_cast; ring
  have e4 : (3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((3 / 2 : ℂ) + t * I) := by
    simp only [map_add, map_mul, map_div₀, map_neg, map_one, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I]; push_cast; ring
  rw [e1, e2, e3, e4, Complex.log_conj _ harg]
  rw [← Complex.norm_conj]
  congr 1
  simp [map_sub, map_add, map_inv₀, map_div₀, map_mul, map_pow, map_ofNat]

/-- The envelope on the whole range `2 ≤ |t|`, from the two leaves and the symmetry. -/
theorem main_term_envelope_of_leaves (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log |t| + 3 / 2 := by
  have pos : ∀ u : ℝ, 2 ≤ u →
      ‖Complex.log ((5 / 2 : ℂ) + u * I) - 1 / (2 * ((5 / 2 : ℂ) + u * I)) -
          1 / (12 * ((5 / 2 : ℂ) + u * I) ^ 2) -
        (((-1 / 2 : ℂ) + u * I)⁻¹ + ((1 / 2 : ℂ) + u * I)⁻¹ + ((3 / 2 : ℂ) + u * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log u + 3 / 2 := by
    intro u hu
    rcases le_total u (5 / 2) with h | h
    · exact main_term_envelope_near u hu h
    · exact main_term_envelope_far u h
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht ⊢
    exact pos t ht
  · rw [abs_of_nonpos h0] at ht ⊢
    have h := pos (-t) ht
    have hn := main_term_norm_neg (-t)
    rw [neg_neg] at hn
    rw [hn]
    exact h

end TailNegMainTerm
end LeanLab.HelfgottMajor.Decomp457b

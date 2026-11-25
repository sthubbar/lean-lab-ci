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

/-- Real part bound for the far range envelope: `0 ≤ re z ≤ log t + 1/4`, from
`re log w = log |w|`, `log |w| ≤ log t + 25/(8 t^2)` and the explicit real parts of the
reciprocal terms. -/
theorem main_term_far_re (t : ℝ) (ht : 5 / 2 ≤ t) :
    0 ≤ (Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
      1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
    (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)).re ∧
    (Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
      1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
    (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)).re
      ≤ Real.log t + 1 / 4 := by
  have hw : (2 * ((5 / 2 : ℂ) + t * I)) = ((5 : ℝ) + (2*t : ℝ) * I : ℂ) := by push_cast; ring
  have hw2 : (12 * ((5 / 2 : ℂ) + t * I) ^ 2) = (((75 : ℝ) - 12 * (t * t) : ℝ) + (60 * t : ℝ) * I : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hn : ‖(5 / 2 : ℂ) + t * I‖ = Real.sqrt (25 / 4 + t * t) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
  rw [hw, hw2]
  simp only [Complex.sub_re, Complex.add_re, Complex.log_re, Complex.inv_re, one_div,
    Complex.normSq_apply, hn]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
  norm_num
  have t0 : 0 < t := by linarith
  have s0 : (25 / 4 : ℝ) ≤ t * t := by nlinarith
  have hpos : (0 : ℝ) < 25 / 4 + t * t := by nlinarith
  rw [Real.log_sqrt hpos.le]
  have hlogt : Real.log (t * t) = 2 * Real.log t := by rw [Real.log_mul t0.ne' t0.ne']; ring
  have hup : Real.log (25 / 4 + t * t) ≤ 2 * Real.log t + 25 / (4 * (t * t)) := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (25 / 4 + t * t) / (t * t) by positivity)
    rw [Real.log_div hpos.ne' (by positivity), hlogt] at h1
    have : (25 / 4 + t * t) / (t * t) - 1 = 25 / (4 * (t * t)) := by field_simp; ring
    linarith
  have hlo : 2 * Real.log t ≤ Real.log (25 / 4 + t * t) := by
    rw [← hlogt]; exact Real.log_le_log (by positivity) (by linarith)
  have hL : 89 / 100 ≤ Real.log t := by
    have h2 := Real.log_two_gt_d9
    have h54 : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
    have hsplit : Real.log (5 / 2 : ℝ) = Real.log 2 + Real.log (5 / 4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have hmono : Real.log (5 / 2 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) ht
    norm_num at h54
    linarith
  have e2 : (25 : ℝ) + 2 * t * (2 * t) = 25 + 4 * (t * t) := by ring
  rw [e2]
  have hc : -(1 / 2 : ℝ) / (1 / 4 + t * t) + 1 / 2 / (1 / 4 + t * t) = 0 := by ring
  rw [hc]
  generalize hS : t * t = S at *
  have hA0 : 0 ≤ 3 / 2 / (9 / 4 + S) := by positivity
  have hA1 : 3 / 2 / (9 / 4 + S) ≤ 3 / 17 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hB0 : 0 ≤ 5 / (25 + 4 * S) := by positivity
  have hB1 : 5 / (25 + 4 * S) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hD : 0 < (75 - 12 * S) * (75 - 12 * S) + 60 * t * (60 * t) := by nlinarith
  have hC0 : (75 - 12 * S) / ((75 - 12 * S) * (75 - 12 * S) + 60 * t * (60 * t)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
  have hC1 : -(1 / 75 : ℝ) ≤ (75 - 12 * S) / ((75 - 12 * S) * (75 - 12 * S) + 60 * t * (60 * t)) := by
    rw [le_div_iff₀ hD]; nlinarith
  have key : 25 / (4 * S) / 2 ≤ 71 / 300 + 5 / (25 + 4 * S) + 3 / 2 / (9 / 4 + S) := by
    have hS0 : 0 < S := by linarith
    have hpoly : 0 ≤ 2272 * S ^ 3 + 15712 * S ^ 2 - 106050 * S - 421875 := by
      nlinarith [mul_pos hS0 hS0, mul_nonneg (mul_nonneg (sub_nonneg.2 s0) (sub_nonneg.2 s0)) hS0.le]
    have hdiff : 71 / 300 + 5 / (25 + 4 * S) + 3 / 2 / (9 / 4 + S) - 25 / (4 * S) / 2 =
        (2272 * S ^ 3 + 15712 * S ^ 2 - 106050 * S - 421875) /
          (600 * S * (25 + 4 * S) * (9 + 4 * S)) := by
      field_simp; ring
    have : 0 ≤ 71 / 300 + 5 / (25 + 4 * S) + 3 / 2 / (9 / 4 + S) - 25 / (4 * S) / 2 := by
      rw [hdiff]; positivity
    linarith
  constructor
  · nlinarith
  · nlinarith

/-- Imaginary part bound for the far range envelope: `|im z| ≤ 21/10`, from
`arg w = arctan (2t/5) = π/4 + arctan ((2t-5)/(2t+5)) ≤ π/4 + (2t-5)/(2t+5)` and the
explicit imaginary parts of the reciprocal terms. -/
theorem main_term_far_im (t : ℝ) (ht : 5 / 2 ≤ t) :
    |(Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
      1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
    (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)).im| ≤ 21 / 10 := by
  have t0 : 0 < t := by linarith
  have hw : (2 * ((5 / 2 : ℂ) + t * I)) = ((5 : ℝ) + (2*t : ℝ) * I : ℂ) := by push_cast; ring
  have hw2 : (12 * ((5 / 2 : ℂ) + t * I) ^ 2) = (((75 : ℝ) - 12 * (t * t) : ℝ) + (60 * t : ℝ) * I : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  -- the argument of w
  have hre : ((5 / 2 : ℂ) + t * I).re = 5 / 2 := by simp
  have him : ((5 / 2 : ℂ) + t * I).im = t := by simp
  have harg : Complex.arg ((5 / 2 : ℂ) + t * I) = Real.arctan (2 * t / 5) := by
    have h1 : |Complex.arg ((5 / 2 : ℂ) + t * I)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by rw [hre]; norm_num))
    rw [abs_lt] at h1
    have h2 := Complex.tan_arg ((5 / 2 : ℂ) + t * I)
    rw [hre, him] at h2
    rw [← Real.arctan_tan h1.1 h1.2, h2]; congr 1; ring
  have hsplit : Real.arctan (2 * t / 5) = Real.pi / 4 + Real.arctan ((2 * t - 5) / (2 * t + 5)) := by
    rw [← Real.arctan_one, Real.arctan_add]
    · congr 1; field_simp; ring
    · rw [one_mul, div_lt_one (by linarith)]; linarith
  have hat : Real.arctan ((2 * t - 5) / (2 * t + 5)) ≤ (2 * t - 5) / (2 * t + 5) :=
    Real.arctan_le_self (div_nonneg (by linarith) (by linarith))
  have hargnn : 0 ≤ Complex.arg ((5 / 2 : ℂ) + t * I) := Complex.arg_nonneg_iff.2 (by rw [him]; linarith)
  have hpi := Real.pi_lt_d4
  rw [hw, hw2]
  simp only [Complex.sub_im, Complex.add_im, Complex.log_im, Complex.inv_im, one_div,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
  norm_num
  have e2 : (25 : ℝ) + 2 * t * (2 * t) = 25 + 4 * (t * t) := by ring
  rw [e2, harg, hsplit]
  have hD : 0 < (75 - 12 * (t * t)) * (75 - 12 * (t * t)) + 60 * t * (60 * t) := by nlinarith
  have hP2 : 60 * t / ((75 - 12 * (t * t)) * (75 - 12 * (t * t)) + 60 * t * (60 * t)) ≤ 1 / 150 := by
    rw [div_le_iff₀ hD]; nlinarith [sq_nonneg (75 - 12 * (t * t))]
  have hP2' : 0 ≤ 60 * t / ((75 - 12 * (t * t)) * (75 - 12 * (t * t)) + 60 * t * (60 * t)) := by
    positivity
  have hP3 : t / (1 / 4 + t * t) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) t0]; nlinarith
  have hP4 : t / (9 / 4 + t * t) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) t0]; nlinarith
  have hP3' : 0 ≤ t / (1 / 4 + t * t) := by positivity
  have hP4' : 0 ≤ t / (9 / 4 + t * t) := by positivity
  have hP1' : 0 ≤ 2 * t / (25 + 4 * (t * t)) := by positivity
  have hy0 : 0 ≤ Real.arctan ((2 * t - 5) / (2 * t + 5)) := by
    exact Real.arctan_nonneg.2 (div_nonneg (by linarith) (by linarith))
  have hpoly : 0 ≤ 307 / 125 * t ^ 4 + 907 / 50 * t ^ 3 - 1093 / 20 * t ^ 2 + 1107 / 8 * t - 375 := by
    have v0 : 0 ≤ t - 5 / 2 := by linarith
    nlinarith [mul_nonneg v0 v0, mul_nonneg (mul_nonneg v0 v0) v0,
      mul_nonneg (mul_nonneg (mul_nonneg v0 v0) v0) v0]
  have hrat : (2 * t - 5) / (2 * t + 5) + 2 * t / (25 + 4 * (t * t)) + 3 * (1 / t) ≤ 1307 / 1000 := by
    have hdiff : 1307 / 1000 - ((2 * t - 5) / (2 * t + 5) + 2 * t / (25 + 4 * (t * t)) + 3 * (1 / t)) =
        (307 / 125 * t ^ 4 + 907 / 50 * t ^ 3 - 1093 / 20 * t ^ 2 + 1107 / 8 * t - 375) /
          (t * (2 * t + 5) * (25 + 4 * (t * t))) := by
      field_simp; ring
    have : 0 ≤ 1307 / 1000 - ((2 * t - 5) / (2 * t + 5) + 2 * t / (25 + 4 * (t * t)) + 3 * (1 / t)) := by
      rw [hdiff]; positivity
    linarith
  simp only [neg_div, sub_neg_eq_add]
  rw [abs_le]
  constructor <;> nlinarith [Real.pi_pos]


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
  obtain ⟨hr0, hr1⟩ := main_term_far_re t ht
  have hi := main_term_far_im t ht
  set z := Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹) with hz
  have hL : 89 / 100 ≤ Real.log t := by
    have h2 := Real.log_two_gt_d9
    have h54 : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
    have hsplit : Real.log (5 / 2 : ℝ) = Real.log 2 + Real.log (5 / 4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have hmono : Real.log (5 / 2 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) ht
    norm_num at h54
    linarith
  have hi2 : z.im ^ 2 ≤ (21 / 10) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hi 2
  have hr2 : z.re ^ 2 ≤ (Real.log t + 1 / 4) ^ 2 := pow_le_pow_left₀ hr0 hr1 2
  have hnorm : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; ring_nf
  have hpos : 0 ≤ Real.log t + 3 / 2 - 2 / 9375 := by linarith
  have hsq : z.re ^ 2 + z.im ^ 2 ≤ (Real.log t + 3 / 2 - 2 / 9375) ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hpos] at this
  rw [hnorm]; linarith

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

import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long
import Batteries.Tactic.OpenPrivate

/-!
Splitting the positive tail energy `principal_log_weight_sq_tail_pos`, the square energy of the
logarithmic derivative weight on `5 < t` bounded by twenty.

The tail is cut once more, at height eight.  On the near piece `5 < t ≤ 8` the interval is short
and only the size of the weight is paid for; on the far piece `8 < t` only the decay is paid for.
Both pieces are compared against the same elementary majorant `(2 log t + 3) ^ 2 / t ^ 2`, whose
primitive `-((2 log t) ^ 2 + 20 log t + 29) / t` gives the two numerical values `3.322` and
`10.988`, and the two budgets four and sixteen add up to twenty.

Every leaf below is one step of that comparison: the pointwise square bound, integrability of the
majorant on each piece, and the two numerical integrals.  The partition identity, the monotone
comparison on each piece and the final addition are proved here, leaving no gap.
-/

/-!
### Helpers for the pointwise square bound `tail_pos_pointwise_sq`

Source P0014 pages 34 and 35, displays 4.13 to 4.15, where the weight is bounded through the
functional equation.  The steps are standard: the functional equation in logarithmic derivative
form `logDeriv_riemannZeta_one_sub`, the von Mangoldt bound four on the line `Re s = 3/2`, the
digamma recurrence, the exact value `tan (-π/4 + i y) = (-1 + i sinh 2y) / cosh 2y`, the exact
imaginary part `(π/2) tanh (π t)` of `ψ(1/2 + i t)`, which cancels against the tangent term, and
the partial fraction series of the digamma function with its first term kept.

Three lemmas already proved in `SPLIT_principal_log_weight_budget` are private there; they are
reused through `open private`, with no change to that file.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
namespace TailPosPointwise
open Complex Contour457

open private logDeriv_three_half_le digamma_half_im_eq digamma_half_re_le from
  LeanLab.HelfgottMajor.SPLIT_principal_log_weight_budget

/-! #### The tangent on the line `Re w = -π/4`, exactly -/

/-- The cosine does not vanish on the line `Re w = -π/4`. -/
theorem cos_neg_pi_div_four_add_mul_I_ne_zero (y : ℝ) :
    Complex.cos ((-(Real.pi / 4) : ℝ) + y * I) ≠ 0 := by
  have e : Complex.cos ((-(Real.pi / 4) : ℝ) + y * I)
      = (((Real.cos (-(Real.pi / 4)) * Real.cosh y : ℝ)) : ℂ)
        + (-((Real.sin (-(Real.pi / 4)) * Real.sinh y : ℝ))) * I := by
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    ring
  intro h
  have hre : (Complex.cos ((-(Real.pi / 4) : ℝ) + y * I)).re
      = Real.cos (-(Real.pi / 4)) * Real.cosh y := by
    rw [e]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Complex.neg_re, Complex.neg_im, neg_zero]
  rw [h, Complex.zero_re, Real.cos_neg, Real.cos_pi_div_four] at hre
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have : 0 < Real.sqrt 2 / 2 * Real.cosh y := mul_pos (by positivity) (Real.cosh_pos y)
  linarith

/-- The tangent on the line `Re w = -π/4`, cleared of its denominator `cosh 2y`. -/
theorem tan_neg_pi_div_four_add_mul_I (y : ℝ) :
    Complex.tan ((-(Real.pi / 4) : ℝ) + y * I) * (Real.cosh (2 * y) : ℂ) = -1 + (Real.sinh (2 * y) : ℂ) * I := by
  have hc := cos_neg_pi_div_four_add_mul_I_ne_zero y
  have hs : Complex.sin (((-(Real.pi / 4)) : ℝ) : ℂ) = ((-(Real.sqrt 2 / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, Real.sin_neg, Real.sin_pi_div_four]
  have hcs : Complex.cos (((-(Real.pi / 4)) : ℝ) : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos, Real.cos_neg, Real.cos_pi_div_four]
  rw [Complex.tan_eq_sin_div_cos, div_mul_eq_mul_div, div_eq_iff hc,
    Complex.sin_add_mul_I, Complex.cos_add_mul_I, hs, hcs]
  have h2c : ((Real.cosh (2 * y) : ℝ) : ℂ) = Complex.cosh y ^ 2 + Complex.sinh y ^ 2 := by
    push_cast
    rw [Complex.cosh_two_mul]
  have h2s : ((Real.sinh (2 * y) : ℝ) : ℂ) = 2 * Complex.sinh y * Complex.cosh y := by
    push_cast
    rw [Complex.sinh_two_mul]
  rw [h2c, h2s]
  have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
  have hq := Complex.cosh_sq (y : ℂ)
  have hr : ((-(Real.sqrt 2 / 2) : ℝ) : ℂ) = -(((Real.sqrt 2 / 2 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_neg]
  rw [hr]
  linear_combination
    (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (-Complex.cosh y - I * Complex.sinh y)) * hq
    - (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (2 * Complex.sinh y ^ 2 * Complex.cosh y)) * hI

/-- The tangent on the line `Re w = -π/4` in real and imaginary parts. -/
theorem tan_neg_pi_div_four_eq (y : ℝ) :
    Complex.tan ((-(Real.pi / 4) : ℝ) + y * I)
      = ((-(1 / Real.cosh (2 * y)) : ℝ) : ℂ) + ((Real.tanh (2 * y) : ℝ) : ℂ) * I := by
  have hC : ((Real.cosh (2 * y) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne'
  have h := tan_neg_pi_div_four_add_mul_I y
  rw [← eq_div_iff hC] at h
  rw [h, Real.tanh_eq_sinh_div_cosh, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_div, Complex.ofReal_one]
  field_simp

/-- The real part of the tangent on the line `Re w = -π/4` is `-1 / cosh 2y`. -/
theorem tan_neg_pi_div_four_re (y : ℝ) :
    (Complex.tan ((-(Real.pi / 4) : ℝ) + y * I)).re = -(1 / Real.cosh (2 * y)) := by
  rw [tan_neg_pi_div_four_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

/-- The imaginary part of the tangent on the line `Re w = -π/4` is `tanh 2y`. -/
theorem tan_neg_pi_div_four_im (y : ℝ) :
    (Complex.tan ((-(Real.pi / 4) : ℝ) + y * I)).im = Real.tanh (2 * y) := by
  rw [tan_neg_pi_div_four_eq]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

/-! #### The real part of `ψ(1/2 + i t)` from below, first term of the series kept -/

section DigammaLower
open DigammaBudget

/-- `1/2 + i t` is not an integer. -/
theorem half_line_mem_integerComplement' (t : ℝ) :
    ((1 / 2 : ℂ) + t * I) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have he : (n : ℝ) = 1 / 2 := by
    have h := congrArg Complex.re hn
    simpa using h
  have h2 : (2 : ℤ) * n = 1 := by
    have hh : (2 : ℝ) * (n : ℝ) = 1 := by rw [he]; norm_num
    exact_mod_cast hh
  omega

/-- `Re ψ(1/2 + i t) ≥ 1/4` for `|t| ≥ 5`, from the partial fraction series with its first
term kept, `Re (1 / (1/2 + i t)) ≤ 2/101` and Euler's constant below `2/3`. -/
theorem digamma_half_re_ge_quarter (t : ℝ) (ht : 5 ≤ |t|) :
    (1 / 4 : ℝ) ≤ (Complex.digamma ((1 / 2 : ℂ) + t * I)).re := by
  have ht2 : (25 : ℝ) ≤ t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  set z : ℂ := (1 / 2 : ℂ) + t * I with hz
  have hzc : z ∈ Complex.integerComplement := by
    rw [hz]; exact half_line_mem_integerComplement' t
  have h := hasSum_digamma_series hzc
  have hterm : ∀ n : ℕ, 0 ≤ ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re := by
    intro n
    have hnorm : ((n : ℝ) + 3 / 2) ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 := Complex.re_le_norm (z + (n : ℂ) + 1)
      have h2 : (z + (n : ℂ) + 1).re = (n : ℝ) + 3 / 2 := by rw [hz]; simp; ring
      rw [h2] at h1
      linarith
    have hinv : |((1 / (z + n + 1) : ℂ)).re| ≤ 1 / ((n : ℝ) + 3 / 2) := by
      have h2 := Complex.abs_re_le_norm ((1 / (z + (n : ℂ) + 1) : ℂ))
      rw [norm_div, norm_one] at h2
      have hpos : (0 : ℝ) < (n : ℝ) + 3 / 2 := by positivity
      calc |((1 / (z + n + 1) : ℂ)).re| ≤ 1 / ‖z + (n : ℂ) + 1‖ := h2
        _ ≤ 1 / ((n : ℝ) + 3 / 2) := by
            apply one_div_le_one_div_of_le hpos hnorm
    have hA : ((1 / ((n : ℂ) + 1) : ℂ)).re = 1 / ((n : ℝ) + 1) := by
      have e : ((n : ℂ) + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) + (0 : ℝ) * I := by push_cast; ring
      rw [one_div, e, inv_re_vertical]
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [Complex.sub_re, hA]
    have h4 : (1 / (z + n + 1) : ℂ).re ≤ 1 / ((n : ℝ) + 3 / 2) := le_trans (le_abs_self _) hinv
    have h5 : 1 / ((n : ℝ) + 3 / 2) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  have hre := Complex.hasSum_re h
  have hge := hre.summable.sum_le_tsum (Finset.range 1) (fun i _ => hterm i)
  have h0 : ∑ n ∈ Finset.range 1, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re
      = 1 - (3 / 2 : ℝ) / ((3 / 2 : ℝ) ^ 2 + t ^ 2) := by
    rw [Finset.sum_range_one]
    have e : z + ((0 : ℕ) : ℂ) + 1 = (((3 / 2 : ℝ) : ℝ) : ℂ) + t * I := by
      rw [hz]; push_cast; ring
    rw [Complex.sub_re, e, one_div (((3 / 2 : ℝ) : ℂ) + t * I), inv_re_vertical]
    simp
  rw [h0] at hge
  have hL : (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z).re
      = ∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re := hre.tsum_eq.symm
  have hzre : (1 / z : ℂ).re = (1 / 2 : ℝ) / ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
    have e : z = (((1 / 2 : ℝ) : ℝ) : ℂ) + t * I := by rw [hz]; push_cast; ring
    rw [e, one_div, inv_re_vertical]
  have hb1 : (3 / 2 : ℝ) / ((3 / 2 : ℝ) ^ 2 + t ^ 2) ≤ 6 / 109 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb2 : (1 / 2 : ℝ) / ((1 / 2 : ℝ) ^ 2 + t ^ 2) ≤ 2 / 101 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hγ : Real.eulerMascheroniConstant ≤ 2 / 3 :=
    le_of_lt Real.eulerMascheroniConstant_lt_two_thirds
  have hEq : (Complex.digamma z).re
      = (∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re)
        - Real.eulerMascheroniConstant - (1 / z : ℂ).re := by
    rw [← hL]
    simp only [Complex.add_re, Complex.ofReal_re]
    ring
  rw [hEq, hzre]
  linarith

end DigammaLower

/-! #### Numerical inputs and the assembly -/

/-- `log 5 ≥ 1.58`, from `log 5 = log (5/4) + 2 log 2` and `log x ≥ 1 - 1/x`. -/
theorem log_five_ge : (1.58 : ℝ) ≤ Real.log 5 := by
  have hsplit : Real.log 5 = Real.log (5 / 4) + Real.log 4 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h54 : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_gt_d9
  norm_num at h54
  linarith

/-- `cosh (π t) ≥ 8` for `t > 5`, from `cosh x ≥ exp x / 2` and `exp x ≥ x + 1`. -/
theorem cosh_pi_mul_ge (t : ℝ) (ht : 5 < t) : (8 : ℝ) ≤ Real.cosh (Real.pi * t) := by
  have h1 := Real.add_one_le_exp (Real.pi * t)
  have h2 := Real.exp_pos (-(Real.pi * t))
  have h3 : (15 : ℝ) < Real.pi * t := by nlinarith [Real.pi_gt_three]
  rw [Real.cosh_eq]
  linarith

/-- The pointwise bound for `ζ'/ζ` on the left line above height five.  Functional equation in
logarithmic derivative form, the bound four on the line `Re s = 3/2`, the digamma recurrence, and
the exact cancellation of the imaginary part of `ψ(1/2 + it)`, which is `(π/2) tanh (π t)`, against
the imaginary part of `(π/2) tan (π s / 2)`. -/
theorem logDeriv_left_half_le_tail (t : ℝ) (ht : 5 < t) :
    ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ≤ 2 * Real.log t + 3 := by
  have ht0 : (0 : ℝ) < t := by linarith
  set s : ℂ := (-1 / 2 : ℂ) + t * I with hs
  have hsre : s.re = -(1 / 2) := by rw [hs]; simp; norm_num
  have hsim : s.im = t := by rw [hs]; simp
  have hsint : ∀ n : ℤ, s ≠ n := by
    intro n hn
    have h := congrArg Complex.re hn
    simp at h
    rw [hsre] at h
    have h2 : (2 : ℤ) * n = -1 := by
      have hh : (2 : ℝ) * (n : ℝ) = -1 := by rw [← h]; norm_num
      exact_mod_cast hh
    omega
  have hz : riemannZeta s ≠ 0 := by
    rw [hs]; simpa using LeanLab.PNTPort.ZetaZeros.zeta_left_ne t
  have hFE := logDeriv_riemannZeta_one_sub hsint hz
  have h1 : ‖logDeriv riemannZeta (1 - s)‖ ≤ 4 := by
    have e : (1 : ℂ) - s = (3 / 2 : ℂ) + (-t) * I := by rw [hs]; push_cast; ring
    rw [e]
    simpa using logDeriv_three_half_le (-t)
  have hsne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    simp at h
    rw [hsre] at h
    have h2 : (2 : ℤ) * (m : ℤ) = 1 := by
      have hh : (2 : ℝ) * (m : ℝ) = 1 := by linarith
      exact_mod_cast hh
    omega
  have hrec := Complex.digamma_apply_add_one s hsne
  have e : s + 1 = (1 / 2 : ℂ) + t * I := by rw [hs]; push_cast; ring
  rw [e] at hrec
  have hEq2 : Complex.digamma s = Complex.digamma ((1 / 2 : ℂ) + t * I) - s⁻¹ := by
    rw [hrec]; ring
  have hT : (Real.pi : ℂ) * s / 2 = ((-(Real.pi / 4) : ℝ) + ((Real.pi * t / 2 : ℝ)) * I) := by
    rw [hs]; push_cast; ring
  have hTre := tan_neg_pi_div_four_re (Real.pi * t / 2)
  have hTim := tan_neg_pi_div_four_im (Real.pi * t / 2)
  have h2y : 2 * (Real.pi * t / 2) = Real.pi * t := by ring
  rw [h2y] at hTre hTim
  have hlogc : Complex.log (2 * Real.pi) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  have hpi2 : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  have hnsq : Complex.normSq s = 1 / 4 + t ^ 2 := by
    rw [Complex.normSq_apply, hsre, hsim]; ring
  have hsinv_re : (s⁻¹).re = -(1 / 2) / (1 / 4 + t ^ 2) := by
    rw [Complex.inv_re, hnsq, hsre]
  have hsinv_im : (s⁻¹).im = -t / (1 / 4 + t ^ 2) := by
    rw [Complex.inv_im, hnsq, hsim]
  have hψim := digamma_half_im_eq t
  have hψlo := digamma_half_re_ge_quarter t (by rw [abs_of_pos ht0]; linarith)
  have hψup := digamma_half_re_le t (by rw [abs_of_pos ht0]; linarith)
  rw [abs_of_pos ht0] at hψup
  set ψ : ℂ := Complex.digamma ((1 / 2 : ℂ) + t * I) with hψ
  set W : ℂ := Complex.log (2 * Real.pi) - ψ + s⁻¹
      + (Real.pi : ℂ) / 2 * Complex.tan (Real.pi * s / 2) with hW
  have hWre : W.re = Real.log (2 * Real.pi) - ψ.re + -(1 / 2) / (1 / 4 + t ^ 2)
      + Real.pi / 2 * (-(1 / Real.cosh (Real.pi * t))) := by
    rw [hW, hT, hlogc, hpi2]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    rw [hTre, hsinv_re]
  have hWim : W.im = -t / (1 / 4 + t ^ 2) := by
    rw [hW, hT, hlogc, hpi2]
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.im_ofReal_mul]
    rw [hTim, hsinv_im, hψim]
    ring
  -- numerical inputs
  have hq : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hlog2pi_up : Real.log (2 * Real.pi) ≤ 2 := LeanLab.PNTPort.ZetaZeros.log_two_pi_le
  have hlog2pi_lo : (1 : ℝ) ≤ Real.log (2 * Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have hlogt : (1.58 : ℝ) ≤ Real.log t :=
    le_trans log_five_ge (Real.log_le_log (by norm_num) ht.le)
  have hlogt3 : Real.log (t + 3) ≤ 2 * Real.log t - 1 := by
    have hle : Real.exp 1 * (t + 3) ≤ t ^ 2 := by
      have he := Real.exp_one_lt_d9
      nlinarith
    have h := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow] at h
    push_cast at h
    linarith
  have hcosh := cosh_pi_mul_ge t ht
  have hsech : Real.pi / 2 * (1 / Real.cosh (Real.pi * t)) ≤ 1 / 5 := by
    have h8 : 1 / Real.cosh (Real.pi * t) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) hcosh
    have h0 : 0 ≤ 1 / Real.cosh (Real.pi * t) := by
      have : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
      positivity
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hsech0 : 0 ≤ Real.pi / 2 * (1 / Real.cosh (Real.pi * t)) := by
    have : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
    have := Real.pi_pos
    positivity
  have hhalf_lo : -(1 / 50 : ℝ) ≤ -(1 / 2) / (1 / 4 + t ^ 2) := by
    rw [le_div_iff₀ hq]; nlinarith
  have hhalf_up : -(1 / 2) / (1 / 4 + t ^ 2) ≤ (0 : ℝ) := by
    apply div_nonpos_of_nonpos_of_nonneg (by norm_num) hq.le
  have hWim_abs : |W.im| ≤ 1 / 5 := by
    rw [hWim, neg_div, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hq]
    nlinarith
  have hWre_abs : |W.re| ≤ 2 * Real.log t - 6 / 5 := by
    rw [hWre, abs_le]
    constructor <;> nlinarith
  have hWnorm : ‖W‖ ≤ 2 * Real.log t - 1 :=
    le_trans (Complex.norm_le_abs_re_add_abs_im W) (by linarith)
  have hsplit : -logDeriv riemannZeta (1 - s) + Complex.log (2 * Real.pi) - Complex.digamma s
        + (Real.pi : ℂ) / 2 * Complex.tan (Real.pi * s / 2)
      = -logDeriv riemannZeta (1 - s) + W := by
    rw [hW, hEq2]; ring
  rw [hFE, hsplit]
  calc ‖-logDeriv riemannZeta (1 - s) + W‖
      ≤ ‖logDeriv riemannZeta (1 - s)‖ + ‖W‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ 2 * Real.log t + 3 := by linarith

/-- The pointwise square bound, from the bound on the logarithmic derivative and
`|-1/2 + i t| ≥ t`. -/
theorem pointwise_sq (t : ℝ) (ht : 5 < t) :
    ‖principalLogWeight t‖ ^ 2 ≤ (2 * Real.log t + 3) ^ 2 / t ^ 2 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hb := logDeriv_left_half_le_tail t ht
  have hnorm : ‖(-1 / 2 : ℂ) + t * I‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hsq : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ (2 * Real.log t + 3) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  unfold principalLogWeight
  rw [norm_div, div_pow, hnorm]
  refine le_trans (div_le_div_of_nonneg_right hsq (by positivity)) ?_
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  nlinarith

end TailPosPointwise
end LeanLab.HelfgottMajor.Decomp457b

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

/-- LEAF. The pointwise square bound on the positive tail: for `5 < t` the square of the
logarithmic derivative weight is at most the elementary majorant `(2 log t + 3) ^ 2 / t ^ 2`.
This is the analytic step, the size of `logDeriv riemannZeta` at `-1/2 + i t` against the size of
`-1/2 + i t`, and it carries all the arithmetic content of the bound. -/
theorem tail_pos_pointwise_sq (t : ℝ) (ht : 5 < t) :
    ‖principalLogWeight t‖ ^ 2 ≤ (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
  TailPosPointwise.pointwise_sq t ht

/-- LEAF. Integrability of the majorant on the near piece `5 < t ≤ 8`.  The majorant is dominated
by a negative power of `t`, so it is integrable on the short interval; this is the hypothesis that
lets the near piece be compared with the weight. -/
theorem tail_pos_majorant_integrableOn_head :
    IntegrableOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioc 5 8) := by
  have hcont : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Icc 5 8) := by
    have hlog : ContinuousOn Real.log (Set.Icc (5 : ℝ) 8) :=
      Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : (5 : ℝ) ≤ x := hx.1
        rintro rfl
        norm_num at h1)
    have hnum : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2) (Set.Icc (5 : ℝ) 8) :=
      ((hlog.const_mul 2).add continuousOn_const).pow 2
    exact hnum.div (continuousOn_id.pow 2) (by
      intro x hx
      have h1 : (5 : ℝ) ≤ x := hx.1
      intro h
      have hx0 : x = 0 := sq_eq_zero_iff.mp h
      linarith)
  exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

/-- The power `t ^ (1/2)` divided by `t ^ 2` is `t ^ (-(3/2))`. -/
private lemma tail_pos_rpow_half_div_sq (t : ℝ) (ht : 0 < t) :
    t ^ (1 / 2 : ℝ) / t ^ 2 = t ^ (-(3 / 2) : ℝ) := by
  rw [div_eq_mul_inv, show (t ^ 2 : ℝ) = t ^ (2 : ℝ) by rw [Real.rpow_two],
    ← Real.rpow_neg ht.le (2 : ℝ), ← Real.rpow_add ht]
  norm_num

/-- The pointwise domination of the majorant by `121 t ^ (-(3/2))` on `8 < t`.  The logarithm
is paid for by a fourth root, which leaves the negative power `-(3/2)` of `t` behind. -/
private lemma tail_pos_majorant_le_rpow (t : ℝ) (ht : 8 < t) :
    (2 * Real.log t + 3) ^ 2 / t ^ 2 ≤ 121 * t ^ (-(3 / 2) : ℝ) := by
  have ht0 : 0 < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlog4 : Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 4)
    calc Real.log t ≤ t ^ (1 / 4 : ℝ) / (1 / 4) := h
      _ = 4 * t ^ (1 / 4 : ℝ) := by ring
  have hpow1 : (1 : ℝ) ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hlogpos : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hb : 2 * Real.log t + 3 ≤ 11 * t ^ (1 / 4 : ℝ) := by nlinarith
  have hb0 : 0 ≤ 2 * Real.log t + 3 := by linarith
  have hsq : (11 * t ^ (1 / 4 : ℝ)) ^ 2 = 121 * t ^ (1 / 2 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast ht0.le]
    norm_num
  have hsqle : (2 * Real.log t + 3) ^ 2 ≤ 121 * t ^ (1 / 2 : ℝ) := by
    nlinarith [hb, hb0, hsq, sq_nonneg (11 * t ^ (1 / 4 : ℝ)),
      sq_nonneg (2 * Real.log t + 3 - 11 * t ^ (1 / 4 : ℝ))]
  have hstep : (2 * Real.log t + 3) ^ 2 / t ^ 2 ≤ 121 * t ^ (1 / 2 : ℝ) / t ^ 2 :=
    div_le_div_of_nonneg_right hsqle (by positivity)
  have heq : 121 * t ^ (1 / 2 : ℝ) / t ^ 2 = 121 * t ^ (-(3 / 2) : ℝ) := by
    rw [show 121 * t ^ (1 / 2 : ℝ) / t ^ 2 = 121 * (t ^ (1 / 2 : ℝ) / t ^ 2) by ring,
      tail_pos_rpow_half_div_sq t ht0]
  linarith [hstep, heq.le, heq.ge]

/-- LEAF. Integrability of the majorant on the far piece `8 < t`.  Here the decay of the majorant
is what is paid for, and again a negative power of `t` dominates it; this is the hypothesis that
lets the far piece be compared with the weight. -/
theorem tail_pos_majorant_integrableOn_far :
    IntegrableOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioi 8) := by
  have hmaj : IntegrableOn (fun t : ℝ => 121 * t ^ (-(3 / 2) : ℝ)) (Set.Ioi 8) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-(3 / 2) : ℝ)) (c := 8) (by norm_num)
      (by norm_num)).const_mul 121
  have hcont : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioi 8) := by
    have hlog : ContinuousOn Real.log (Set.Ioi (8 : ℝ)) :=
      Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : (8 : ℝ) < x := hx
        rintro rfl
        norm_num at h1)
    have hnum : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2) (Set.Ioi (8 : ℝ)) :=
      ((hlog.const_mul 2).add continuousOn_const).pow 2
    exact hnum.div (continuousOn_id.pow 2) (by
      intro x hx
      have h1 : (8 : ℝ) < x := hx
      intro h
      have hx0 : x = 0 := sq_eq_zero_iff.mp h
      linarith)
  refine Integrable.mono' hmaj (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hnn : (0 : ℝ) ≤ (2 * Real.log t + 3) ^ 2 / t ^ 2 := by
    have h1 : (0 : ℝ) < t := by linarith [Set.mem_Ioi.mp ht]
    positivity
  rw [Real.norm_of_nonneg hnn]
  exact tail_pos_majorant_le_rpow t ht

/-- The primitive of the majorant: differentiating `-((2 log t)^2 + 20 log t + 29) / t` gives
`(2 log t + 3)^2 / t^2`. -/
private lemma hasDerivAt_tail_pos_primitive (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => -(((2 * Real.log s) ^ 2 + 20 * Real.log s + 29) / s))
      ((2 * Real.log t + 3) ^ 2 / t ^ 2) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.log s) (2 * t⁻¹) t := hlog.const_mul 2
  have h4 : HasDerivAt (fun s : ℝ => 20 * Real.log s) (20 * t⁻¹) t := hlog.const_mul 20
  have hA := ((h2.pow 2).add h4).add_const 29
  have hq := hA.div (hasDerivAt_id t) ht.ne'
  refine (hq.neg).congr_deriv ?_
  norm_num
  field_simp
  ring

/-- The logarithm squared over the identity tends to zero. -/
private lemma tail_pos_tendsto_log_sq_div (n : ℕ) :
    Filter.Tendsto (fun t : ℝ => Real.log t ^ n / t) Filter.atTop (nhds 0) :=
  (Real.isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero

/-- The primitive of the majorant tends to zero at infinity. -/
private lemma tendsto_tail_pos_primitive :
    Filter.Tendsto (fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t)) Filter.atTop (nhds 0) := by
  have h2 : Filter.Tendsto (fun t : ℝ => (2 * Real.log t) ^ 2 / t) Filter.atTop (nhds 0) := by
    have hbase := (tail_pos_tendsto_log_sq_div 2).const_mul (4 : ℝ)
    have hfun : (fun t : ℝ => (2 * Real.log t) ^ 2 / t)
        = fun t : ℝ => 4 * (Real.log t ^ 2 / t) := by
      funext t
      ring
    rw [hfun]
    simpa using hbase
  have h20 : Filter.Tendsto (fun t : ℝ => 20 * Real.log t / t) Filter.atTop (nhds 0) := by
    have hbase := (tail_pos_tendsto_log_sq_div 1).const_mul (20 : ℝ)
    have hfun : (fun t : ℝ => 20 * Real.log t / t)
        = fun t : ℝ => 20 * (Real.log t ^ 1 / t) := by
      funext t
      ring
    rw [hfun]
    simpa using hbase
  have h29 : Filter.Tendsto (fun t : ℝ => 29 / t) Filter.atTop (nhds 0) := by
    have hbase := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (29 : ℝ)
    have hfun : (fun t : ℝ => 29 / t) = fun t : ℝ => 29 * t⁻¹ := by
      funext t
      rw [div_eq_mul_inv]
    rw [hfun]
    simpa using hbase
  have hsum := ((h2.add h20).add h29).neg
  have hfun : (fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
      = fun t : ℝ => -((2 * Real.log t) ^ 2 / t + 20 * Real.log t / t + 29 / t) := by
    funext t
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
  rw [hfun]
  simpa using hsum

/-- The value of the majorant integral on the far piece, from the primitive. -/
private lemma integral_tail_pos_far :
    (∫ t in Set.Ioi (8 : ℝ), (2 * Real.log t + 3) ^ 2 / t ^ 2)
      = (4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29) / 8 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
    (f' := fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (a := 8) (m := 0)
    (fun x hx => hasDerivAt_tail_pos_primitive x (by linarith [Set.mem_Ici.mp hx]))
    tail_pos_majorant_integrableOn_far tendsto_tail_pos_primitive
  rw [h]
  ring

/-- The value of the majorant integral on the near piece, from the primitive. -/
private lemma integral_tail_pos_head :
    (∫ t in Set.Ioc (5 : ℝ) 8, (2 * Real.log t + 3) ^ 2 / t ^ 2)
      = (4 * (Real.log 5) ^ 2 + 20 * Real.log 5 + 29) / 5 -
        (4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29) / 8 := by
  have hle : (5 : ℝ) ≤ 8 := by norm_num
  rw [← intervalIntegral.integral_of_le hle]
  have hint : IntervalIntegrable (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) volume 5 8 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr tail_pos_majorant_integrableOn_head
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
    (f' := fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (a := 5) (b := 8)
    (fun x hx => hasDerivAt_tail_pos_primitive x (by
      rw [Set.uIcc_of_le hle] at hx
      have h1 : (5 : ℝ) ≤ x := hx.1
      linarith))
    hint
  rw [h]
  ring

/-- The logarithm of five is at most `1.637`, from `log 5 = log (5/4) + 2 log 2`. -/
private lemma tail_pos_log_five_le : Real.log 5 ≤ 1.637 := by
  have hsplit : Real.log 5 = Real.log (5 / 4) + Real.log 4 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h54 : Real.log (5 / 4) ≤ 5 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  nlinarith [Real.log_two_lt_d9, hsplit, h54, h4]

/-- The logarithm of eight is three times the logarithm of two. -/
private lemma tail_pos_log_eight_eq : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  ring

/-- The elementary majorant at `log 8` is at most `128`. -/
private lemma tail_pos_A_log_eight_upper :
    4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29 ≤ 128 := by
  have heq := tail_pos_log_eight_eq
  have h1 : Real.log 8 ≤ 3 * 0.6931471808 := by
    rw [heq]
    nlinarith [Real.log_two_lt_d9]
  have h0 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- The elementary majorant at `log 8` is at least `87.8`. -/
private lemma tail_pos_A_log_eight_lower :
    87.8 ≤ 4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29 := by
  have heq := tail_pos_log_eight_eq
  have h1 : 3 * 0.6931471803 ≤ Real.log 8 := by
    rw [heq]
    nlinarith [Real.log_two_gt_d9]
  have h0 : 0 ≤ Real.log 8 := le_trans (by norm_num) h1
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- The elementary majorant at `log 5` is at most `72.5`. -/
private lemma tail_pos_A_log_five_upper :
    4 * (Real.log 5) ^ 2 + 20 * Real.log 5 + 29 ≤ 72.5 := by
  have h1 : Real.log 5 ≤ 1.637 := tail_pos_log_five_le
  have h0 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- LEAF. The numerical value of the near piece: the integral of the majorant over `5 < t ≤ 8` is
at most four.  The primitive is `-((2 log t) ^ 2 + 20 log t + 29) / t`, which gives the value
`3.322` for this piece, and the budget four leaves room. -/
theorem tail_pos_majorant_head_le :
    (∫ t in Set.Ioc 5 8, (2 * Real.log t + 3) ^ 2 / t ^ 2) ≤ 4 := by
  rw [integral_tail_pos_head]
  have h5 := tail_pos_A_log_five_upper
  have h8 := tail_pos_A_log_eight_lower
  linarith

/-- LEAF. The numerical value of the far piece: the integral of the majorant over `8 < t` is at
most sixteen.  The same primitive gives the value `10.988` for this piece, and the budget sixteen
leaves room. -/
theorem tail_pos_majorant_far_le :
    (∫ t in Set.Ioi 8, (2 * Real.log t + 3) ^ 2 / t ^ 2) ≤ 16 := by
  rw [integral_tail_pos_far]
  have h8 := tail_pos_A_log_eight_upper
  linarith

/-- The positive tail `5 < t` splits at height eight into the near piece and the far piece. -/
private theorem tail_pos_region :
    (Set.Ioi (5 : ℝ)) = Set.Ioc 5 8 ∪ Set.Ioi 8 := by
  ext t
  simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
  constructor
  · intro h
    by_cases h8 : t ≤ 8
    · exact Or.inl ⟨h, h8⟩
    · exact Or.inr (by linarith)
  · rintro (⟨h, _⟩ | h)
    · exact h
    · linarith

/-- The two pieces of the positive tail are disjoint. -/
private theorem tail_pos_disjoint :
    Disjoint (Set.Ioc (5 : ℝ) 8) (Set.Ioi 8) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [Set.mem_Ioc] at hx
  rw [Set.mem_Ioi] at hx'
  linarith

/-- The square energy over the positive tail is the sum of the energies over the two pieces.  The
pieces are disjoint and measurable and the squared weight is integrable, so the integral splits. -/
private theorem tail_pos_decomp :
    (∫ t in Set.Ioi (5 : ℝ), ‖principalLogWeight t‖ ^ 2) =
      (∫ t in Set.Ioc 5 8, ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Ioi 8, ‖principalLogWeight t‖ ^ 2) := by
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  rw [tail_pos_region,
    setIntegral_union tail_pos_disjoint measurableSet_Ioi hint.integrableOn hint.integrableOn]

/-- The square energy of the logarithmic derivative weight on the positive tail `5 < t` is at most
twenty.  The tail is cut at height eight, each piece is compared with the elementary majorant
using the pointwise bound, and the two numerical integrals four and sixteen add up to twenty. -/
theorem principal_log_weight_sq_tail_pos_split :
    (∫ t in Set.Ioi 5, ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  classical
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hhead : (∫ t in Set.Ioc 5 8, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioc 5 8, (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
    setIntegral_mono_on hint.integrableOn tail_pos_majorant_integrableOn_head measurableSet_Ioc
      (fun t ht => tail_pos_pointwise_sq t (Set.mem_Ioc.mp ht).1)
  have hfar : (∫ t in Set.Ioi 8, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioi 8, (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
    setIntegral_mono_on hint.integrableOn tail_pos_majorant_integrableOn_far measurableSet_Ioi
      (fun t ht => tail_pos_pointwise_sq t (by linarith [Set.mem_Ioi.mp ht]))
  rw [tail_pos_decomp]
  linarith [hhead, hfar, tail_pos_majorant_head_le, tail_pos_majorant_far_le]

end LeanLab.HelfgottMajor.Decomp457b

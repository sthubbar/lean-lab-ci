import Mathlib

/-!
Split of the leaf `TailNegMainTerm.main_term_envelope_near`, P0014, Helfgott, Major arcs for
Goldbach's problem, arXiv 1305.2897, page 34 display 4.10, near range `2 ≤ t ≤ 5/2`.
The complex logarithm of `w = 5/2 + it` is rewritten here in real form,
`log w = log |w| + i arcsin (t / |w|)`, valid since `re w > 0`; this identity is proved.
The remaining real variable envelope is one smaller LEAF.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
namespace TailNegMainTerm
open Complex

/-- The complex logarithm of `5/2 + it` in real form, real part `log sqrt (25/4 + t^2)` and
imaginary part `arcsin (t / sqrt (25/4 + t^2))`, since the real part `5/2` is positive. -/
theorem log_five_halves_real_form (t : ℝ) :
    Complex.log ((5 / 2 : ℂ) + t * I) =
      ((Real.log (Real.sqrt (25 / 4 + t ^ 2)) : ℝ) : ℂ) +
        ((Real.arcsin (t / Real.sqrt (25 / 4 + t ^ 2)) : ℝ) : ℂ) * I := by
  have hre : ((5 / 2 : ℂ) + t * I).re = 5 / 2 := by simp
  have him : ((5 / 2 : ℂ) + t * I).im = t := by simp
  have hn : ‖(5 / 2 : ℂ) + t * I‖ = Real.sqrt (25 / 4 + t ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, him]
    congr 1; ring
  apply Complex.ext
  · simp only [Complex.log_re, hn, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · rw [Complex.log_im, Complex.arg_of_re_nonneg (by rw [hre]; norm_num), him, hn]
    simp

/-- LEAF: the elementary envelope of P0014 page 34 display 4.10, near range `2 ≤ t ≤ 5/2`,
in real form: with `log w = log |w| + i arcsin (t/|w|)` for `w = 5/2 + it`, the Stirling main
term minus the three recurrence terms, plus `2/9375`, is at most `log t + 3/2`.
Numerically the margin is `0.00040` at `t = 2` and `0.226` at `t = 5/2`.
Class HARD: a sharp real variable inequality on a compact range, rigorous numerics for
`Real.log` and `Real.arcsin` to about four digits near `t = 2`. -/
theorem main_term_envelope_near_real (t : ℝ) (ht : 2 ≤ t) (ht' : t ≤ 5 / 2) :
    ‖((Real.log (Real.sqrt (25 / 4 + t ^ 2)) : ℝ) : ℂ) +
          ((Real.arcsin (t / Real.sqrt (25 / 4 + t ^ 2)) : ℝ) : ℂ) * I -
          1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log t + 3 / 2 := by
  sorry

end TailNegMainTerm
end LeanLab.HelfgottMajor.Decomp457b

import Mathlib
import LeanLab.HelfgottMajor.SPLIT_S3_main_term_envelope_far

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
  exact LeanLab.HelfgottMajor.SplitS3EnvFar.main_term_envelope_near_proof t ht ht'

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
  exact LeanLab.HelfgottMajor.SplitS3EnvFar.main_term_envelope_far_proof t ht

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

#print axioms LeanLab.HelfgottMajor.Decomp457b.TailNegMainTerm.main_term_envelope_far
#print axioms LeanLab.HelfgottMajor.Decomp457b.TailNegMainTerm.main_term_envelope_near

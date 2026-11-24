import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long

/-!
Splitting the digamma input `Decomp457b.principal_log_weight_tail_neg_digamma_envelope` of
the negative tail split of P0014, Helfgott, Major arcs for Goldbach's problem,
arXiv 1305.2897: for `2 ≤ |t|`, `‖ψ(-1/2 + it)‖ ≤ log |t| + 3/2`.

The statement is true but tight: numerically `‖ψ(-1/2 + 2i)‖ = 2.192474` against
`log 2 + 3/2 = 2.193147`, a margin of `0.00067` at `t = 2`, and the margin grows with `|t|`.
So the route must be sharp near height two.

Route, the gamma factor step of the paper, P0014 page 34 display 4.10, where Binet's formula
for the digamma function is quoted:
* the recurrence `ψ(s + 3) = ψ(s) + 1/s + 1/(s+1) + 1/(s+2)` at `s = -1/2 + it`, proved here
  from Mathlib's `Complex.digamma_apply_add_nat`;
* LEAF, Stirling with two correction terms at `w = 5/2 + it`:
  `‖ψ(w) - (log w - 1/(2w) - 1/(12 w^2))‖ ≤ 1/(120 (5/2)^4) = 2/9375`;
* LEAF, the elementary envelope: for `2 ≤ |t|` the explicit main term plus `2/9375` is at most
  `log |t| + 3/2`; numerically its worst margin is `0.00040`, at `t = 2`.
The parent follows by the triangle inequality. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Complex

/-- LEAF: Stirling's expansion of the digamma function with two correction terms, the gamma
factor step of P0014 page 34 display 4.10, where Binet's formula DLMF 5.9.13 to 5.9.15 is
quoted, specialised to the line of real part five halves. With
`ψ(w) = log w - 1/(2w) - ∫_0^∞ f(x) e^{-wx} dx`, `f(x) = 1/(e^x - 1) - 1/x + 1/2`, DLMF 5.9.13,
and `0 ≤ x/12 - f(x) ≤ x^3/720` for `x > 0`, the remainder after `-1/(12 w^2)` is at most
`∫_0^∞ x^3/720 e^{-(5/2)x} dx = 1/(120 (5/2)^4) = 2/9375` in modulus.
Numerically the true remainder is at most `0.37` of the bound on this line.
Class HARD: needs the Binet Laplace form of digamma and the Laplace transform estimate. -/
theorem tail_neg_digamma_stirling_five_half (t : ℝ) :
    ‖Complex.digamma ((5 / 2 : ℂ) + t * I) -
        (Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2))‖ ≤ 2 / 9375 := by
  sorry

/-- LEAF: the elementary envelope closing the gamma factor step of P0014 page 34 display
4.10 on the line of real part minus one half. With `s = -1/2 + it` and `w = s + 3`, the
explicit Stirling main term `log w - 1/(2w) - 1/(12 w^2)` minus the recurrence terms
`1/s + 1/(s+1) + 1/(s+2)`, plus the remainder budget `2/9375`, is at most `log |t| + 3/2`
for `2 ≤ |t|`. Numerically the worst margin is `0.00040`, at `|t| = 2`, rising to `0.38`
by `|t| = 3`; so near height two the argument of `w` and the logarithm need about four
correct digits. Class HARD: a sharp real variable inequality on an unbounded range. -/
theorem tail_neg_digamma_main_term_envelope (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log |t| + 3 / 2 := by
  sorry

/-- The recurrence step, proved: `ψ(-1/2 + it + 3) = ψ(-1/2 + it) + Σ_{k<3} 1/(-1/2 + it + k)`. -/
theorem tail_neg_digamma_recurrence (t : ℝ) :
    Complex.digamma ((5 / 2 : ℂ) + t * I) =
      Complex.digamma ((-1 / 2 : ℂ) + t * I) +
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹) := by
  have hs : ∀ m : ℕ, ((-1 / 2 : ℂ) + t * I) ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    simp at h
    have h2 : (2 : ℝ) * m = 1 := by linarith
    have h3 : (2 * m : ℕ) = 1 := by exact_mod_cast h2
    omega
  have h := Complex.digamma_apply_add_nat hs 3
  have e : ((-1 / 2 : ℂ) + t * I) + ((3 : ℕ) : ℂ) = (5 / 2 : ℂ) + t * I := by
    push_cast; ring
  rw [e] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  ring_nf

/-- The parent `principal_log_weight_tail_neg_digamma_envelope`, assembled from the two
leaves and the recurrence by the triangle inequality. -/
theorem principal_log_weight_tail_neg_digamma_envelope_of_leaves (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 3 / 2 := by
  have hrec := tail_neg_digamma_recurrence t
  have hS := tail_neg_digamma_stirling_five_half t
  have hM := tail_neg_digamma_main_term_envelope t ht
  set w : ℂ := (5 / 2 : ℂ) + t * I
  set M : ℂ := Complex.log w - 1 / (2 * w) - 1 / (12 * w ^ 2)
  set S3 : ℂ := ((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹
  have hd : Complex.digamma ((-1 / 2 : ℂ) + t * I) =
      (Complex.digamma w - M) + (M - S3) := by
    rw [hrec]; ring
  rw [hd]
  calc ‖(Complex.digamma w - M) + (M - S3)‖
      ≤ ‖Complex.digamma w - M‖ + ‖M - S3‖ := norm_add_le _ _
    _ ≤ 2 / 9375 + ‖M - S3‖ := by gcongr
    _ ≤ Real.log |t| + 3 / 2 := by linarith

end LeanLab.HelfgottMajor.Decomp457b

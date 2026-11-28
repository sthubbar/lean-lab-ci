import LeanLab.HelfgottMajor.SPLIT_border_principal_logDeriv_le_of_one_le_re

/-!
# Split of `border_principal_logDeriv_le_near_one` (`HelfgottMajor/SPLIT_border_principal_logDeriv_le_of_one_le_re`)

The target bounds `‖g'/g‖` by `11.7` for `g(s) = (s - 1) ζ(s)`, Mathlib's `LFunctionTrivChar₁ 1`,
on the border points of the box `[-1/4, 5/4] x [-3/2, 3/2]` with `1 ≤ Re u ≤ 6/5`.

The cut is the quotient `g'/g` itself.  On this border the condition `1 ≤ Re u ≤ 6/5` leaves
only the two short horizontal pieces `Im u = ± 3/2`, proved below.  There the target follows from
a lower bound for `‖g‖` and an upper bound for `‖g'‖`:

* `norm_LFunctionTrivChar₁_one_ge_near_one`: `‖(u - 1) ζ(u)‖ ≥ 1/2` on the two pieces,
  a nonvanishing statement for `ζ` near `1 ± 3i/2`; mpmath on 201 points per piece gives a
  minimum of `1.2149`;
* `norm_deriv_LFunctionTrivChar₁_one_le_near_one`: `‖g'(u)‖ ≤ 5` on the two pieces; mpmath gives
  a maximum of `0.6766`.

The twin `border_principal_logDeriv_le_near_one_of_leaves` proves the target statement verbatim
from the two leaves, as `5 / (1/2) = 10 ≤ 11.7`.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitPrincipalNearOne

open Real Complex
open LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF: the lower bound `‖(u - 1) ζ(u)‖ ≥ 1/2` on the two short pieces `1 ≤ Re u ≤ 6/5`,
`Im u = ± 3/2`, the denominator step of the target `border_principal_logDeriv_le_near_one`;
MEDIUM: provable from the Euler Maclaurin formula
`ζ(s) = ∑_{n < N} n^{-s} + N^{1-s}/(s - 1) + N^{-s}/2 - s ∫_N^∞ ({x} - 1/2) x^{-s-1} dx`,
Titchmarsh, The Theory of the Riemann Zeta Function, display 2.1.5 to 2.1.6 and section 4.2, with
a small `N` and interval arithmetic on the two segments.  mpmath gives the minimum `1.2149`. -/
theorem norm_LFunctionTrivChar₁_one_ge_near_one (u : ℂ) (h1 : 1 ≤ u.re) (h2 : u.re ≤ 6 / 5)
    (him : u.im = 3 / 2 ∨ u.im = -(3 / 2)) :
    (1 / 2 : ℝ) ≤ ‖DirichletCharacter.LFunctionTrivChar₁ 1 u‖ := by
  sorry

/-- LEAF: the upper bound `‖g'(u)‖ ≤ 5` for `g(s) = (s - 1) ζ(s)` on the two short pieces
`1 ≤ Re u ≤ 6/5`, `Im u = ± 3/2`, the numerator step of the target
`border_principal_logDeriv_le_near_one`; MEDIUM: from `g' = ζ + (s - 1) ζ'` and the Euler
Maclaurin formula of Titchmarsh section 2.1 and 4.2 differentiated in `s`, or from Cauchy's
estimate for `g` on a small circle.  mpmath gives the maximum `0.6766`. -/
theorem norm_deriv_LFunctionTrivChar₁_one_le_near_one (u : ℂ) (h1 : 1 ≤ u.re)
    (h2 : u.re ≤ 6 / 5) (him : u.im = 3 / 2 ∨ u.im = -(3 / 2)) :
    ‖deriv (DirichletCharacter.LFunctionTrivChar₁ 1) u‖ ≤ 5 := by
  sorry

/-- The border points of the box `[-1/4, 5/4] x [-3/2, 3/2]` with `1 ≤ Re u ≤ 6/5` lie on the
two horizontal sides `Im u = ± 3/2`.  Proved. -/
theorem border_im_of_near_one {u : ℂ}
    (hu : u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ))
    (h1 : 1 ≤ u.re) (h2 : u.re ≤ 6 / 5) : u.im = 3 / 2 ∨ u.im = -(3 / 2) := by
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff]
    at hu
  rcases hu with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
  · right; rw [h]; norm_num
  · have : u.re = -1/4 := h
    linarith
  · left; rw [h]
  · have : u.re = 5/4 := h
    linarith

/-- The target `SplitPrincipalBorder.border_principal_logDeriv_le_near_one`, verbatim, from the
two leaves: `‖g'/g‖ ≤ 5 / (1/2) = 10 ≤ 11.7`. -/
theorem border_principal_logDeriv_le_near_one_of_leaves :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      1 ≤ u.re → u.re ≤ 6 / 5 →
      ‖logDeriv (DirichletCharacter.LFunctionTrivChar₁ 1) u‖ ≤ 11.7 := by
  intro u hu h1 h2
  have him := border_im_of_near_one hu h1 h2
  have hg := norm_LFunctionTrivChar₁_one_ge_near_one u h1 h2 him
  have hd := norm_deriv_LFunctionTrivChar₁_one_le_near_one u h1 h2 him
  have hgpos : (0 : ℝ) < ‖DirichletCharacter.LFunctionTrivChar₁ 1 u‖ := by linarith
  rw [logDeriv_apply, norm_div, div_le_iff₀ hgpos]
  nlinarith

end LeanLab.HelfgottMajor.SplitPrincipalNearOne

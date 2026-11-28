import LeanLab.HelfgottMajor.SPLIT_border_principal_logDeriv_le_near_one

/-!
# Split of `norm_deriv_LFunctionTrivChar₁_one_le_near_one` (`HelfgottMajor/SPLIT_border_principal_logDeriv_le_near_one`)

The target bounds `‖g'(u)‖` by `5` for `g(s) = (s - 1) ζ(s)`, Mathlib's `LFunctionTrivChar₁ 1`,
on the two short pieces `1 ≤ Re u ≤ 6/5`, `Im u = ± 3/2`.

The cut is Cauchy's estimate for the derivative, Titchmarsh, The Theory of Functions, section
2.5, in Mathlib `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`: `g` is entire, Mathlib
`DirichletCharacter.differentiable_LFunctionTrivChar₁`, so on the circle of radius `1/2` about
`u` a bound `‖g‖ ≤ 5/2` gives `‖g'(u)‖ ≤ (5/2) / (1/2) = 5`.  Those circles lie in the two boxes
`1/2 ≤ Re w ≤ 17/10`, `1 ≤ |Im w| ≤ 2`, proved below, and the one leaf is the size of `g` there:

* `norm_LFunctionTrivChar₁_one_le_box`: `‖(w - 1) ζ(w)‖ ≤ 5/2` on the two boxes; mpmath on a
  61 by 51 grid per box gives a maximum of `1.8286`.

The twin `norm_deriv_LFunctionTrivChar₁_one_le_near_one_of_leaves` proves the target statement
verbatim from the leaf.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitPrincipalDerivCauchy

open Real Complex Metric

/-- LEAF: the size of `g(s) = (s - 1) ζ(s)` on the boxes `1/2 ≤ Re w ≤ 17/10`, `1 ≤ |Im w| ≤ 2`,
the input of Cauchy's estimate for the numerator step of `border_principal_logDeriv_le_near_one`;
MEDIUM: from the Euler Maclaurin formula
`ζ(s) = ∑_{n < N} n^{-s} + N^{1-s}/(s - 1) - s ∫_N^∞ {x} x^{-s-1} dx`, Titchmarsh, The Theory of
the Riemann Zeta Function, display 2.1.5 and section 4.2, with a small `N`, each term bounded
in norm by elementary estimates.  mpmath gives the maximum `1.8286`. -/
theorem norm_LFunctionTrivChar₁_one_le_box (w : ℂ) (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 17 / 10)
    (h3 : 1 ≤ |w.im|) (h4 : |w.im| ≤ 2) :
    ‖DirichletCharacter.LFunctionTrivChar₁ 1 w‖ ≤ 5 / 2 := by
  sorry

/-- Points of the circle of radius `1/2` about a point of the two short pieces lie in the two
boxes of the leaf.  Proved. -/
theorem sphere_subset_box {u w : ℂ} (h1 : 1 ≤ u.re) (h2 : u.re ≤ 6 / 5)
    (him : u.im = 3 / 2 ∨ u.im = -(3 / 2)) (hw : w ∈ sphere u (1 / 2)) :
    1 / 2 ≤ w.re ∧ w.re ≤ 17 / 10 ∧ 1 ≤ |w.im| ∧ |w.im| ≤ 2 := by
  rw [mem_sphere, dist_eq_norm] at hw
  have hre := Complex.abs_re_le_norm (w - u)
  have him' := Complex.abs_im_le_norm (w - u)
  rw [hw, Complex.sub_re] at hre
  rw [hw, Complex.sub_im] at him'
  rw [abs_le] at hre him'
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rcases him with h | h
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_le]
    rcases him with h | h <;> constructor <;> linarith

/-- The target `SplitPrincipalNearOne.norm_deriv_LFunctionTrivChar₁_one_le_near_one`, verbatim,
from the leaf by Cauchy's estimate on the circle of radius `1/2`. -/
theorem norm_deriv_LFunctionTrivChar₁_one_le_near_one_of_leaves (u : ℂ) (h1 : 1 ≤ u.re)
    (h2 : u.re ≤ 6 / 5) (him : u.im = 3 / 2 ∨ u.im = -(3 / 2)) :
    ‖deriv (DirichletCharacter.LFunctionTrivChar₁ 1) u‖ ≤ 5 := by
  have hd : DiffContOnCl ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) (ball u (1 / 2)) :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).diffContOnCl
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 2)
    hd (C := 5 / 2) (fun w hw => by
      obtain ⟨a, b, c, d⟩ := sphere_subset_box h1 h2 him hw
      exact norm_LFunctionTrivChar₁_one_le_box w a b c d)
  calc _ ≤ (5 / 2 : ℝ) / (1 / 2) := h
    _ = 5 := by norm_num

end LeanLab.HelfgottMajor.SplitPrincipalDerivCauchy

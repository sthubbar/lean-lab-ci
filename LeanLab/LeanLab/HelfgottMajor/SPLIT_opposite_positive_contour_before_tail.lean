import LeanLab.HelfgottMajor.Decomp511a

/-!
Split of `opposite_positive_contour_before_tail` of `HelfgottMajor/Decomp511a.lean`.

The target bounds the twisted Gaussian Mellin norm at positive real part by three terms:

* the central contribution, `mainCoefficient σ |im| δ` times the saddle exponential
  `exp (-E (|im| / (π * δ) ^ 2) * |im|)`;
* the contribution of the initial part of the deformed contour, `firstCoefficient σ
  |im|` times `exp (-0.4798 * |im|)`;
* the real Gaussian tail from the endpoint `min (|im| / (2 * π * |δ|)) (5 / 4 * sqrt
  |im|)`, left unevaluated.

The cut below is the cut the statement itself displays. The Mellin integral over
`Ioi 0` is written as the integral over `Ioc 0 a` plus the integral over `Ioi a`,
where `a` is that same endpoint, and the two parts are bounded separately:

* the lower part is everything the deformed contour has to do before it returns to
  the real axis at `a`, so it carries the saddle, the initial segment and the phase
  damping;
* the upper part is exactly the real Gaussian tail of the statement, and only the
  unit modulus twist is lost to the norm.

Nothing in either leaf mentions the other part, so no leaf restates the target, and
the assembly is interval additivity plus the triangle inequality.

Degenerate values, checked before the cut was kept.  The sign hypothesis
`δ * s.im < 0` gives `δ ≠ 0` and `s.im ≠ 0`, so `|s.im| / (2 * π * |δ|)` and
`(π * δ) ^ 2` never divide by zero, and the endpoint `a` is strictly positive at every
height the hypotheses allow, so neither of the two integrals is over the empty set and
`x ^ (s.re - 1)` is not read at `x = 0` as a limit.  The height bound `100 ≤ |s.im|`
excludes the small height cases in which the endpoint geometry degenerates.  Both
hypotheses are satisfiable together: `δ = -1` and `s = 1 / 2 + 100 * I` give
`δ * s.im = -100 < 0` and `|s.im| = 100`, hence `a = min (100 / (2 * π)) (5 / 4 * 10)`,
a positive real number.  The strip bound `s.re ≤ 1` allows `s.re = 1`, where
`x ^ (s.re - 1)` is `1` and the tail integrand is the plain Gaussian; it also allows
s.re close to `0`, where `x ^ (s.re - 1)` is unbounded near `0` but the lower integral
is still over `Ioc 0 a`, and it is the leaf that carries that endpoint singularity, not
the tail.  A negative `δ` and a negative imaginary part leave `|s.im|`,
`(π * δ) ^ 2` and `min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)` unchanged, so
both leaves are invariant under `δ ↦ -δ` and `s ↦ conj s`.
-/

namespace LeanLab.HelfgottMajor.Decomp511a
open Real SplitGaussian123 Filter
open scoped Topology

/-- LEAF.  The lower part of the contour, up to the endpoint where it returns to the
real axis.  This is the quantitative central saddle estimate together with the initial
segment estimate: the part of the Mellin integral below
`a = min (|im| / (2 * π * |δ|)) (5 / 4 * sqrt |im|)` is bounded by the saddle term of the
statement plus the initial segment term of the statement.  It says nothing about the
tail beyond `a`, so it is strictly easier than the target, and the target does not
imply it without the tail bound.  The hypotheses are satisfiable, for instance at
`δ = -1` and `s = 1 / 2 + 100 * I`, where the interval of integration is
`Ioc 0 (5 / 4 * 10)` and both sides are finite reals. -/
theorem leaf_lower_contour_estimate (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖∫ x : ℝ in Set.Ioc (0 : ℝ) (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  sorry

/-- LEAF.  The real Gaussian tail beyond the endpoint.  The twist
`e (δ * x)` has modulus one at real `x`, and the Mellin power has modulus
`x ^ (re - 1)`, so the norm of the tail integral is at most the real Gaussian tail that
the statement keeps unevaluated.  This is one inequality about one integral, it does not
bound the rest of the contour, and its hypotheses are satisfiable at every positive
endpoint: at `a = 1`, `δ = 0` and `s = 1 / 2` both sides are positive real numbers. -/
theorem leaf_real_tail_estimate (δ : ℝ) (s : ℂ) (a : ℝ) (ha : 0 < a) :
    ‖∫ x : ℝ in Set.Ioi a, (x : ℂ) ^ (s - 1) *
        ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ ≤
      ∫ x : ℝ in Set.Ioi a, exp (-x ^ 2 / 2) * x ^ (s.re - 1) := by
  sorry

/-- The contour reduction with the real tail left unevaluated, assembled from the two
leaves.  The Mellin integral is the sum of its two parts at the endpoint `a`, and each
part is bounded by its own leaf; what is left is the arithmetic of the three terms. -/
theorem opposite_positive_contour_before_tail_split (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) +
      (∫ x : ℝ in Set.Ioi (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        exp (-x ^ 2 / 2) * x ^ (s.re - 1)) := by
  have htpos : 0 < |s.im| := by linarith
  have hd : δ ≠ 0 := by rintro rfl; simp at hsign
  have habs : 0 < |δ| := abs_pos.mpr hd
  have hsqt : 0 < sqrt |s.im| := sqrt_pos.mpr htpos
  have ha : 0 < min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|) :=
    lt_min (div_pos htpos (by positivity)) (by positivity)
  have hF : MeasureTheory.IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) *
      ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))) (Set.Ioi 0) := by
    simpa only [smul_eq_mul] using
      LeanLab.HelfgottMajor.Decomp511b.twisted_mellin_integrable δ s hσ0
  have hmel : gaussianMellin δ s = ∫ x : ℝ in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
      ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x)) := by
    simp only [gaussianMellin, mellin, smul_eq_mul]
  have hsplit : (∫ x : ℝ in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
        ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))) =
      (∫ x : ℝ in Set.Ioc (0 : ℝ) (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
          (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))) +
        (∫ x : ℝ in Set.Ioi (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
          (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le,
      MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact hF.mono_set Set.Ioc_subset_Ioi_self
    · exact hF.mono_set (Set.Ioi_subset_Ioi ha.le)
  rw [hmel, hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := leaf_lower_contour_estimate δ s hσ0 hσ1 ht hsign
  have h2 := leaf_real_tail_estimate δ s
    (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)) ha
  linarith only [h1, h2]

end LeanLab.HelfgottMajor.Decomp511a

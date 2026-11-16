import LeanLab.HelfgottMajor.SPLIT_opposite_positive_contour_before_tail

/-!
Split of `leaf_lower_contour_estimate` of
`HelfgottMajor/SPLIT_opposite_positive_contour_before_tail.lean`.

The target bounds the norm of the lower part of the deformed contour, the Mellin
integral over `Set.Ioc 0 (min (|im| / (2 * π * |δ|)) (5 / 4 * sqrt |im|))`, by the
central saddle term plus the initial segment term.  Two separate analytic inputs
are spent there:

* the segment of the contour that leaves the origin at 45 degrees, which is where
  the `firstCoefficient` term is spent;
* the remainder, the steepest descent piece together with the return to the real
  axis, which is where the `mainCoefficient` term is spent.

The cut below keeps the two inputs apart.  The initial segment is written as the
truncated 45 degree ray integral of `Decomp511b.rotatedKernel`; it is one explicit
complex number once the segment length `r` is fixed, and the first leaf bounds it.
The remainder is the difference between the real integral and that ray integral,
and the second leaf bounds it; the existence of a segment length short enough for
the phase to be dominated is part of that second leaf, since the length used in the
deformation is not an elementary function of the statement's parameters.

Neither leaf mentions the other and neither implies the target: the first bounds
only the ray, the second only the difference.  The assembly is the triangle
inequality `‖G‖ = ‖(G - J) + J‖ ≤ ‖G - J‖ + ‖J‖`, together with the reflection
symmetry of the statement, which reads the case `im s < 0` off the case `0 < im s`
after `δ ↦ -δ` and `s ↦ conj s`: the interval endpoint, `|s.im|`, `(π * δ) ^ 2`
and both coefficients are unchanged by that substitution.

Degenerate values.  The sign hypothesis `δ * s.im < 0` gives `δ ≠ 0` and
`s.im ≠ 0`, so `|s.im| / (2 * π * |δ|)` and `(π * δ) ^ 2` never divide by zero, the
endpoint `min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)` is strictly positive
at every admissible argument, and the interval of integration is never empty.
`100 ≤ |s.im|` excludes the small height cases.  The hypotheses of both leaves are
satisfiable: `δ = -1` and `s = 1 / 2 + 100 * I` have `δ * s.im = -100 < 0`,
`|s.im| = 100`, and `r = 1` satisfies the segment length condition
`0.4798 * 100 + 2 * π * 1 / sqrt 2 ≤ (π / 4) * 100` with room to spare, so the ray
integral of the first leaf is over `Set.Ioc 0 1`.  The strip bound allows
`s.re = 1`, where `x ^ (s.re - 1)` is `1`, and `s.re` close to `0`, where the
integrand is unbounded near the origin; the first leaf carries that endpoint.
-/

namespace LeanLab.HelfgottMajor.Decomp511a
open Real SplitGaussian123 Filter
open scoped Topology

/-- LEAF.  The initial 45 degree segment of the deformed contour, bounded by the
first error term.  The integrand is the `Decomp511b.rotatedKernel` at angle
`π / 4`, whose modulus is `x ^ (re s - 1) * exp (-2 * π * δ * x / sqrt 2)`, so the
factor `w ^ s` with `w = (1 + I) / sqrt 2` contributes `exp (-(π / 4) * im s)` and
the phase condition on the segment length turns the remaining exponential into
`exp (-0.4798 * |im s|)`.  The constant `1 + (1 + sqrt 2) / |im s|` is what the
integration by parts of the small real part case produces.  This leaf bounds only
the ray, never the rest of the contour, and it is stated in the normal form
`0 < im s`; the reflected normal form is not needed because the assembly reduces to
this one by conjugation. -/
theorem leaf_initial_segment_ray_bound (δ : ℝ) (s : ℂ) (r : ℝ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) (hspos : 0 < s.im) (hr : 0 < r)
    (hexp : 0.4798 * |s.im| + 2 * π * |δ| * r / Real.sqrt 2 ≤ π / 4 * |s.im|) :
    ‖(((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
        (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
          LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t)‖ ≤
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  sorry

/-- LEAF.  The central saddle piece.  There is a segment length `r`, short enough
for the phase condition and at most `sqrt |im s|`, such that the lower contour
integral minus the 45 degree ray integral of that length is bounded by the central
term.  That difference is the steepest descent arc together with its return to the
real axis, and it is strictly smaller than the real integral it is taken from: this
leaf says nothing about the ray itself, so it does not imply the target.  The
hypotheses are satisfiable, for instance at `δ = -1` and `s = 1 / 2 + 100 * I`
with a short `r`, and the statement is a single inequality about one complex
number. -/
theorem leaf_saddle_piece_exists (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) (hspos : 0 < s.im) :
    ∃ r : ℝ, 0 < r ∧ r ≤ sqrt |s.im| ∧
      0.4798 * |s.im| + 2 * π * |δ| * r / Real.sqrt 2 ≤ π / 4 * |s.im| ∧
      ‖(∫ x : ℝ in Set.Ioc (0 : ℝ) (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
          (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x)))
        - (((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
          (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
            LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t)‖ ≤
        mainCoefficient s.re |s.im| δ *
          exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) := by
  sorry

/-- The positive height normal form of the target, from the two leaves.  The lower
contour integral is the ray integral plus its difference from the real integral,
and the two leaves bound those two summands separately. -/
private theorem lower_contour_positive (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) (hspos : 0 < s.im) :
    ‖∫ x : ℝ in Set.Ioc (0 : ℝ) (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  obtain ⟨r, hr, _hrs, hexp, hrem⟩ := leaf_saddle_piece_exists δ s hσ0 hσ1 ht hsign hspos
  have hray := leaf_initial_segment_ray_bound δ s r hσ0 hσ1 ht hsign hspos hr hexp
  set G : ℂ := ∫ x : ℝ in Set.Ioc (0 : ℝ)
      (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x)) with hG
  set J : ℂ := (((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
      (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
        LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t) with hJ
  have hsplit : (G - J) + J = G := by ring
  have htri : ‖G‖ ≤ ‖G - J‖ + ‖J‖ := by
    have hle := norm_add_le (G - J) J
    rwa [hsplit] at hle
  linarith only [htri, hrem, hray]

/-- The contour reduction of the lower part of the deformed contour, assembled from
the two leaves.  The positive height case is the triangle inequality above; the
negative height case is the same inequality read through conjugation, which leaves
the endpoint, both coefficients and the rate unchanged. -/
theorem leaf_lower_contour_estimate_split (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖∫ x : ℝ in Set.Ioc (0 : ℝ) (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
  by_cases hspos : 0 < s.im
  · exact lower_contour_positive δ s hσ0 hσ1 ht hsign hspos
  · push_neg at hspos
    have hne : s.im ≠ 0 := by
      intro h
      have h100 : (100 : ℝ) ≤ 0 := by
        rw [h] at ht
        simpa using ht
      norm_num at h100
    have hneg : s.im < 0 := lt_of_le_of_ne hspos hne
    have hconjpos : 0 < (starRingEnd ℂ s).im := by
      simpa using hneg
    have hsign' : (-δ) * (starRingEnd ℂ s).im < 0 := by
      have h : (-δ) * (starRingEnd ℂ s).im = δ * s.im := by
        simp only [Complex.conj_im]
        ring
      rw [h]
      exact hsign
    have h := lower_contour_positive (-δ) (starRingEnd ℂ s)
      (by simpa using hσ0) (by simpa using hσ1) (by simpa using ht) hsign' hconjpos
    have h' : ‖∫ x : ℝ in Set.Ioc (0 : ℝ)
          (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
          (x : ℂ) ^ ((starRingEnd ℂ s) - 1) *
            ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e ((-δ) * x))‖ ≤
        mainCoefficient s.re |s.im| δ *
          exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
        firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
      have hR : mainCoefficient ((starRingEnd ℂ) s).re |((starRingEnd ℂ) s).im| (-δ) *
            exp (-BookE.E (|((starRingEnd ℂ) s).im| / (π * -δ) ^ 2) *
              |((starRingEnd ℂ) s).im|) +
          firstCoefficient ((starRingEnd ℂ) s).re |((starRingEnd ℂ) s).im| *
            exp (-0.4798 * |((starRingEnd ℂ) s).im|) =
          mainCoefficient s.re |s.im| δ *
            exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
            firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) := by
        have h1 : (π * (-δ)) ^ 2 = (π * δ) ^ 2 := by ring
        simp only [Complex.conj_re, Complex.conj_im, abs_neg, mainCoefficient, h1]
      simpa only [Complex.conj_im, abs_neg] using (h.trans (le_of_eq hR))
    have hconj : (∫ x : ℝ in Set.Ioc (0 : ℝ)
          (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
          (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x)))
        = starRingEnd ℂ (∫ x : ℝ in Set.Ioc (0 : ℝ)
          (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
          (x : ℂ) ^ ((starRingEnd ℂ s) - 1) *
            ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e ((-δ) * x))) := by
      rw [← integral_conj]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hx0 : 0 < x := hx.1
      have hp : starRingEnd ℂ ((x : ℂ) ^ ((starRingEnd ℂ s) - 1)) =
          (x : ℂ) ^ (s - 1) := by
        have hc := Complex.cpow_conj (x : ℂ) ((starRingEnd ℂ s) - 1)
          (by simpa only [Complex.arg_ofReal_of_nonneg hx0.le] using pi_ne_zero.symm)
        have h2 : starRingEnd ℂ (starRingEnd ℂ s) = s := by
          simpa using star_star s
        have h1 : starRingEnd ℂ ((starRingEnd ℂ s) - 1) = s - 1 := by
          rw [map_sub, map_one, h2]
        rw [h1] at hc
        simp only [Complex.conj_ofReal] at hc
        exact hc.symm
      have he : starRingEnd ℂ (LeanLab.HelfgottArcs.e ((-δ) * x)) =
          LeanLab.HelfgottArcs.e (δ * x) := by
        unfold LeanLab.HelfgottArcs.e
        rw [← Complex.exp_conj]
        congr 1
        simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
        push_cast
        ring
      simp only [map_mul, he, hp, Complex.conj_ofReal]
    rw [hconj, Complex.norm_conj]
    exact h'

import LeanLab.HelfgottMajor.SPLIT_leaf_lower_contour_estimate

/-!
Refutation route for `leaf_saddle_piece_exists` of
`HelfgottMajor/SPLIT_leaf_lower_contour_estimate.lean`, burst-20261124 agent S2G5.

The leaf asks for a segment length `r` such that the real integral `G` over
`(0, X]`, `X = min (|τ| / (2 π |δ|)) (5/4 sqrt |τ|)`, minus the 45 degree ray integral
`J` of length `r`, is bounded by the central term
`mainCoefficient σ |τ| δ * exp (-E (|τ| / (π δ) ^ 2) * |τ|)`.

At `δ = -1/1000`, `s = 1/2 + 3000 i` the endpoint is `X = 5/4 sqrt 3000`, and by Cauchy
on the sector `0 < |z| < X`, `0 < arg z < π / 4`, the difference `G - J` is the rest
of the ray, from `r w` to `X w`, plus the arc of radius `X` from angle `π / 4` down to
`0`.  The arc carries the endpoint term `|f(X)| / |f'/f (X)|` of size about
`exp (-25 * 3000 / 32)`, while the central term is about `exp (-0.78532 * 3000)`:
`25 / 32 = 0.78125` is below `E`, so the endpoint term wins.

Numerical check, mpmath at 50 digits, path ray plus arc, burst-20261124 S2G5:
`|arc| = 1.8718e-1021`, the whole ray from `0` to `X w` has norm at most
`2 sqrt X * exp (-750 π) * exp (2 π X / (1000 sqrt 2)) = 1.1711e-1022`, and the
central term is `8.3712e-1024`.  So for every admissible `r` the norm of `G - J` is at
least `1.755e-1021`, which is more than `209` times the central term; at 23 sampled
`r` in `(0, sqrt 3000]` the computed ratio is `225.0` to `226.2`.

The leaf below is that numerical fact, stated as a strict inequality for every
admissible `r`; the theorem after it, proved, shows it refutes the universal
statement of `leaf_saddle_piece_exists`.  No existing statement is changed.
-/

namespace LeanLab.HelfgottMajor.Decomp511a
open Real SplitGaussian123

/-- The counterexample point `s = 1/2 + 3000 i`. -/
private theorem s2g5_re : ((1 / 2 : ℂ) + 3000 * Complex.I).re = 1 / 2 := by simp

private theorem s2g5_im : ((1 / 2 : ℂ) + 3000 * Complex.I).im = 3000 := by simp

/-- LEAF: refutation of `leaf_saddle_piece_exists` at `δ = -1/1000`, `s = 1/2 + 3000 i`,
P0014 page 24, the truncation of the real integral at `5/4 sqrt τ` before display 3.59.
For every segment length `r` admitted by the leaf, the real integral minus the 45 degree
ray integral exceeds the central term: by Cauchy the difference is the ray from `r w`
to `X w` plus the arc of radius `X = 5/4 sqrt 3000`, the arc has norm `1.8718e-1021`,
the ray at most `1.1711e-1022`, the central term is `8.3712e-1024`.  HARD -/
theorem leaf_saddle_piece_counterexample (r : ℝ) (hr : 0 < r)
    (hrs : r ≤ sqrt |((1 / 2 : ℂ) + 3000 * Complex.I).im|)
    (hexp : 0.4798 * |((1 / 2 : ℂ) + 3000 * Complex.I).im| + 2 * π * |(-1 / 1000 : ℝ)| * r /
      Real.sqrt 2 ≤ π / 4 * |((1 / 2 : ℂ) + 3000 * Complex.I).im|) :
    mainCoefficient ((1 / 2 : ℂ) + 3000 * Complex.I).re |((1 / 2 : ℂ) + 3000 * Complex.I).im|
        (-1 / 1000) *
      exp (-BookE.E (|((1 / 2 : ℂ) + 3000 * Complex.I).im| / (π * (-1 / 1000)) ^ 2) *
        |((1 / 2 : ℂ) + 3000 * Complex.I).im|) <
    ‖(∫ x : ℝ in Set.Ioc (0 : ℝ)
          (min (|((1 / 2 : ℂ) + 3000 * Complex.I).im| / (2 * π * |(-1 / 1000 : ℝ)|))
            (5 / 4 * sqrt |((1 / 2 : ℂ) + 3000 * Complex.I).im|)),
          (x : ℂ) ^ (((1 / 2 : ℂ) + 3000 * Complex.I) - 1) *
            ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e ((-1 / 1000) * x)))
        - (((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + 3000 * Complex.I)) *
          (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
            LeanLab.HelfgottMajor.Decomp511b.rotatedKernel (-1 / 1000) (π / 4)
              ((1 / 2 : ℂ) + 3000 * Complex.I) t)‖ := by
  sorry

/-- The universal statement of `leaf_saddle_piece_exists` is false, given the
counterexample leaf: its hypotheses hold at `δ = -1/1000`, `s = 1/2 + 3000 i`, and any
witness `r` contradicts the leaf. -/
theorem leaf_saddle_piece_exists_refuted :
    ¬ ∀ (δ : ℝ) (s : ℂ), 0 < s.re → s.re ≤ 1 → 100 ≤ |s.im| → δ * s.im < 0 → 0 < s.im →
      ∃ r : ℝ, 0 < r ∧ r ≤ sqrt |s.im| ∧
        0.4798 * |s.im| + 2 * π * |δ| * r / Real.sqrt 2 ≤ π / 4 * |s.im| ∧
        ‖(∫ x : ℝ in Set.Ioc (0 : ℝ) (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
            (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x)))
          - (((1 + Complex.I) / (Real.sqrt 2 : ℝ) : ℂ) ^ s) *
            (∫ t : ℝ in Set.Ioc (0 : ℝ) r,
              LeanLab.HelfgottMajor.Decomp511b.rotatedKernel δ (π / 4) s t)‖ ≤
          mainCoefficient s.re |s.im| δ *
            exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) := by
  intro h
  obtain ⟨r, hr, hrs, hexp, hle⟩ := h (-1 / 1000) ((1 / 2 : ℂ) + 3000 * Complex.I)
    (by rw [s2g5_re]; norm_num) (by rw [s2g5_re]; norm_num)
    (by rw [s2g5_im]; norm_num [abs_of_pos]) (by rw [s2g5_im]; norm_num) (by rw [s2g5_im]; norm_num)
  have hlt := leaf_saddle_piece_counterexample r hr hrs hexp
  linarith

end LeanLab.HelfgottMajor.Decomp511a

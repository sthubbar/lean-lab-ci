import LeanLab.HelfgottMajor.SPLIT_tail_mass_integral

/-!
Splitting the pointwise envelope `Decomp269c.mass_pointwise_envelope` into three steps.

The target bounds one zero's multiplicity weighted Mellin mass by `4.226` times the sum of the
exponential decay branch `exp (-0.1598 * |im|)` and, for nonzero shift, the Gaussian decay branch
`exp (-0.1065 * (|im| / (π * |δ|)) ^ 2)`. The right hand side carries no multiplicity factor, so
the pointwise bound is a product of two inputs: the analytic decay of the Gaussian Mellin
transform along the critical strip, and the smallness of the analytic multiplicity against that
decay.

* `strip_mellin_decay` is the analytic input: the Mellin transform decays like `exp (-0.78 * |im|)`
  on the open strip above height `100`, with the half moment constant `2.15581`.
* `zero_multiplicity_subexponential` is the bookkeeping input: a zero above height `100` has
  multiplicity at most `exp (0.6 * |im|)`, far below the zero count.
* `multiplicity_decay_product_le` is the arithmetic input: the product of the multiplicity rate
  with the decay still fits under `exp (-0.1598 * t)` for `t` at least `100`.

The assembly multiplies the first two, applies the third, and drops the nonnegative Gaussian
branch into the bracket. `mass_pointwise_envelope` itself is not used.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. The analytic step: on the open critical strip, above height `100`, the Gaussian Mellin
transform is bounded by the half moment constant `2.15581` times the exponential decay
`exp (-0.78 * |s.im|)`, uniformly in the real shift. The shift only enters through a phase of
modulus one, so it cannot increase the norm. This estimate involves no zero of `L (s, χ)`. -/
theorem strip_mellin_decay (δ : ℝ) (s : ℂ) (hre0 : 0 < s.re) (hre1 : s.re < 1)
    (him : 100 ≤ |s.im|) :
    ‖gaussianMellin δ s‖ ≤ 2.15581 * exp (-0.78 * |s.im|) := by
  sorry

/-- LEAF. The multiplicity step: a zero of `L (s, χ)` in the open critical strip above height
`100` has analytic multiplicity at most the exponential `exp (0.6 * |s.im|)` of its height. The
zero count gives a multiplicity that is polynomial in the height, so the rate `0.6` is well
above what is needed, and the height restriction `100` keeps the small heights out. -/
theorem zero_multiplicity_subexponential (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : DirichletCharacter.LFunction χ s = 0) (hre0 : 0 < s.re) (hre1 : s.re < 1)
    (him : 100 ≤ |s.im|) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) s : ℝ) ≤ exp (0.6 * |s.im|) := by
  sorry

/-- LEAF. The arithmetic step: for a height `t` at least `100` the product of the multiplicity
rate `exp (0.6 * t)` with the decay envelope `2.15581 * exp (-0.78 * t)` fits under the single
exponential `exp (-0.1598 * t)` of the target. Only the two rates and the constant are compared
here; no analytic input is used. -/
theorem multiplicity_decay_product_le (t : ℝ) (ht : 100 ≤ t) :
    exp (0.6 * t) * (2.15581 * exp (-0.78 * t)) ≤ exp (-0.1598 * t) := by
  sorry

/-- The pointwise envelope, assembled from the three steps. The mass is the multiplicity times
the norm of the Mellin transform, the decay and the multiplicity bound are multiplied, the
arithmetic step puts the product under `exp (-0.1598 * |im|)`, and the nonnegative Gaussian
branch is absorbed into the bracket, which is then scaled by the constant `4.226`. -/
theorem mass_pointwise_envelope_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : 100 ≤ T) :
    ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      mellinMassTerm χ δ ρ.val ≤
        4.226 * (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  intro ρ
  have him : 100 ≤ |ρ.val.im| := le_trans hT (le_of_lt ρ.property.2.2.2)
  have hre0 : 0 < ρ.val.re := ρ.property.2.1
  have hre1 : ρ.val.re < 1 := ρ.property.2.2.1
  have hdec : ‖gaussianMellin δ ρ.val‖ ≤ 2.15581 * exp (-0.78 * |ρ.val.im|) :=
    strip_mellin_decay δ ρ.val hre0 hre1 him
  have hord : (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) ≤
      exp (0.6 * |ρ.val.im|) :=
    zero_multiplicity_subexponential q χ ρ.val ρ.property.1 hre0 hre1 him
  have hprod : exp (0.6 * |ρ.val.im|) * (2.15581 * exp (-0.78 * |ρ.val.im|)) ≤
      exp (-0.1598 * |ρ.val.im|) := multiplicity_decay_product_le |ρ.val.im| him
  have hmass : mellinMassTerm χ δ ρ.val ≤
      exp (0.6 * |ρ.val.im|) * (2.15581 * exp (-0.78 * |ρ.val.im|)) := by
    unfold mellinMassTerm
    exact mul_le_mul hord hdec (norm_nonneg _) (Real.exp_pos _).le
  have hgauss : 0 ≤ (if δ = 0 then 0 else
      exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
    split
    · exact le_refl 0
    · exact (Real.exp_pos _).le
  have hsum : (0 : ℝ) ≤ exp (-0.1598 * |ρ.val.im|) +
      (if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) :=
    add_nonneg (Real.exp_pos _).le hgauss
  have hscale : exp (-0.1598 * |ρ.val.im|) +
      (if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
      4.226 * (exp (-0.1598 * |ρ.val.im|) +
        if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
    have h1 : (1 : ℝ) ≤ 4.226 := by norm_num
    have := mul_le_mul_of_nonneg_right h1 hsum
    simpa [one_mul] using this
  exact (hmass.trans hprod).trans (le_trans (le_add_of_nonneg_right hgauss) hscale)

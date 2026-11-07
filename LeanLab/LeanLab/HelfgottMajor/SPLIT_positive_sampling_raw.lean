import LeanLab.HelfgottMajor.Decomp431a

/-!
Split of the positive signed zero sampling inequality of `Decomp431a.positive_sampling_raw`.

The sealed inequality bounds the positive signed Mellin mass attached to the zeros of a
primitive Dirichlet `L`-function in the strip `0 < re < 1` below height `T`, with imaginary
part above `1`, by a sum of three terms: a main term carrying the square root of the
critical line energy and the square root of the squared logarithmic height weight, an error
term carrying the square root of the derivative energy and the square root of the squared
shifted log weight, and an endpoint term at height `1`.

The split proceeds in two stages.  First the signed mass is replaced by the sum of the
absolute values of its summands, so that every summand enters with a sign (stage one).
Second, that nonnegative zero sum is turned into three line integrals over the height
interval `[1, T]` (stage two).  The two square root factors are then obtained by Cauchy
Schwarz on the height interval: one against the critical line energy, one against the
derivative energy above height `1`.  Each leaf below is one of those steps.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF. Stage one, sign removal: the positive signed zero mass is at most the sum over the
same zero set of the absolute values of its summands, each restricted to imaginary part
above `1`.  This is the triangle inequality for a nonnegative summand family; it uses no
analytic input and no hypothesis on the zeros. -/
theorem positive_mass_le_norm_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    positiveMass χ δ T ≤
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ := by
  sorry

/-- LEAF. Stage two, zero sum to line integral: the nonnegative sum of the Mellin masses at
the positive zeros below height `T` is at most the sum of the three height integrals over
`[1, T]` that appear on the right: the mean weight integral of the critical line values, the
integral of the derivative values against the shifted log weight, and the endpoint value at
height `1` against the log of the modulus.  This is the sampling step; it produces linear
weights and no square root factor yet. -/
theorem positive_mass_norm_sum_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) := by
  sorry

/-- LEAF. Cauchy Schwarz on the height interval against the critical line energy: the mean
weight integral of the critical line values, divided by `2 * π`, is at most the square root
of the line energy times the square root of the squared logarithmic weight integral.  Only
`[1, T]` inside the positive half line is used, so this leaf has no character or zero
hypothesis; it is a two function estimate with a nonnegative pair. -/
theorem main_weight_cauchy_schwarz (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) ≤
      sqrt (lineEnergy δ 1) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) := by
  sorry

/-- LEAF. Cauchy Schwarz on the height interval above height `1` against the derivative
energy: the integral of the derivative values against the shifted log weight is at most the
square root of the derivative energy times the square root of the squared shifted log weight
integral.  This leaf carries no character, zero or main term input. -/
theorem error_weight_cauchy_schwarz (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) ≤
      sqrt (derivativeEnergy δ 1) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) := by
  sorry

/-- The positive signed zero sampling inequality, assembled from the four leaves: sign
removal, zero sum to line integral, and the two interval Cauchy Schwarz estimates. -/
theorem positive_sampling_raw_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    positiveMass χ δ T ≤
      sqrt (lineEnergy δ 1) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ 1) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
  have h1 := positive_mass_le_norm_sum q χ δ T
  have h2 := positive_mass_norm_sum_integral q χ hχ δ T hT hlarge hzeros
  have h3 := main_weight_cauchy_schwarz q δ T hT
  have h4 := error_weight_cauchy_schwarz q δ T hT
  exact h1.trans (h2.trans (add_le_add (add_le_add h3 h4) le_rfl))

end LeanLab.HelfgottMajor.Decomp431a

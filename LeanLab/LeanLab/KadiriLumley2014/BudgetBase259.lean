/-
P0059 arXiv 1407.7902v1 page 4 and page 5 Proposition 2.3.
Propagation of a zero budget certificate from X0 to larger X.
AI wrote this Lean code. CODEX task301. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroDefinitions259
import LeanLab.KadiriLumley2014.WeightTail
import LeanLab.KadiriLumley2014.ParameterMonotonicity

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory
open Task64 Task92

/-- The complete normalized error side of Proposition 2.3 for the polynomial weight. -/
noncomputable def normalizedBudget (m : ℕ) (δ u X a : ℝ) : ℝ :=
  zeroError m δ u X + u / (2 * (Real.exp u - 1) * X ^ 2) +
    (2.05022 * 10 ^ (-3 : ℤ)) / ((Real.exp u - 1) * Real.sqrt X) +
    (2 * (1 + δ) * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t)) *
      (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)))

/-- Page 4 after equation 2.18. Every term of the normalized error decreases with X.
This implication is CONDITIONAL ON summability at X0. -/
theorem normalizedBudget_antitone (m : ℕ) {δ u X0 X a : ℝ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hX0 : 0 < X0) (hX : X0 ≤ X)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hgap : 1 < X0 * (Real.exp u - 1))
    (hs : Summable (zeroSummand m δ u X0)) :
    normalizedBudget m δ u X a ≤ normalizedBudget m δ u X0 a := by
  have hXpos : 0 < X := hX0.trans_le hX
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hz := (zeroError_antitone m δ u hX0 hX hs).2
  have hsquare : X0 ^ 2 ≤ X ^ 2 := by nlinarith
  have hr : u / (2 * (Real.exp u - 1) * X ^ 2) ≤
      u / (2 * (Real.exp u - 1) * X0 ^ 2) := by
    apply div_le_div_of_nonneg_left hu.le (by positivity)
    exact mul_le_mul_of_nonneg_left hsquare (by positivity)
  have homega : (2.05022 * 10 ^ (-3 : ℤ)) / ((Real.exp u - 1) * Real.sqrt X) ≤
      (2.05022 * 10 ^ (-3 : ℤ)) / ((Real.exp u - 1) * Real.sqrt X0) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX) he.le
  have hcoef : 0 ≤ 2 * (1 + δ) * tailMass m a /
      (∫ t in (0 : ℝ)..1, weight m t) := by
    exact div_nonneg (mul_nonneg (by positivity) (tailMass_bounds m ha ha2).1)
      (weight_mass_pos m).le
  have htail := mul_le_mul_of_nonneg_left
    (tail_ratio_antitone hu hδ hX0 hX hgap) hcoef
  unfold normalizedBudget
  linarith

/-- A strict certificate at X0 remains strict for every larger X.
This implication is CONDITIONAL ON summability and the certificate at X0. -/
theorem normalizedBudget_lt_of_base (m : ℕ) {δ u X0 X a : ℝ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hX0 : 0 < X0) (hX : X0 ≤ X)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hgap : 1 < X0 * (Real.exp u - 1))
    (hs : Summable (zeroSummand m δ u X0))
    (hbudget : normalizedBudget m δ u X0 a < 1 + δ / 2) :
    normalizedBudget m δ u X a < 1 + δ / 2 :=
  (normalizedBudget_antitone m hδ hu hX0 hX ha ha2 hgap hs).trans_lt hbudget

/-- Clearing the positive normalizing factor gives the exact unnormalized zero budget. -/
theorem normalizedBudget_lt_iff (m : ℕ) (δ a : ℝ) {u X : ℝ}
    (hu : 0 < u) (hX : 0 < X) :
    normalizedBudget m δ u X a < 1 + δ / 2 ↔
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
        tailCoefficient δ u X * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) +
        u / (2 * X) <
      (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hC : 0 < (Real.exp u - 1) * X := mul_pos he hX
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hr : ((Real.exp u - 1) * X) * (u / (2 * (Real.exp u - 1) * X ^ 2)) =
      u / (2 * X) := by
    field_simp
  have homega : ((Real.exp u - 1) * X) *
      ((2.05022 * 10 ^ (-3 : ℤ)) / ((Real.exp u - 1) * Real.sqrt X)) =
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X := by
    field_simp
    nlinarith [Real.sq_sqrt hX.le]
  have htail : ((Real.exp u - 1) * X) *
      ((2 * (1 + δ) * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t)) *
        (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)))) =
      tailCoefficient δ u X * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) := by
    unfold tailCoefficient
    ring
  have hscale : ((Real.exp u - 1) * X) * normalizedBudget m δ u X a =
      ((Real.exp u - 1) * X) * zeroError m δ u X + u / (2 * X) +
        (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
        tailCoefficient δ u X * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) := by
    unfold normalizedBudget
    rw [mul_add, mul_add, mul_add, hr, homega, htail]
  constructor
  · intro h
    have hh := mul_lt_mul_of_pos_left h hC
    rw [hscale] at hh
    nlinarith
  · intro h
    apply (mul_lt_mul_iff_right₀ hC).mp
    rw [hscale]
    nlinarith

end LeanLab.KadiriLumley2014.Task301

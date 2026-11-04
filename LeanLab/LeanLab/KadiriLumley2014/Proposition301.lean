/-
P0059 arXiv 1407.7902v1 page 5 Proposition 2.3 equation 2.20.
The prime conclusion is CONDITIONAL ON the named analytic inputs and a base certificate.
AI wrote this Lean code. CODEX task301. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.Budget301

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory
open Task64 Task92

/-- Proposition 2.3 with each required analytic input explicit.
CONDITIONAL ON CostaEstimate, the psi lower bound, the endpoint upper bound
and the certified normalized budget at X0. -/
theorem prime_of_base_budget (hCosta : CostaEstimate) (m : ℕ) {δ u X0 X a : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX0 : Real.exp 38 ≤ X0) (hX : X0 ≤ X)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hgap : 1 < X0 * (Real.exp u - 1))
    (hs : Summable (zeroSummand m δ u X0))
    (hbudget : normalizedBudget m δ u X0 a < 1 + δ / 2)
    (hpsi : (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) - u / (2 * X) ≤
      psiAverage m δ u X)
    (htail : tailThetaIntegral m δ u X a ≤ tailCoefficient δ u X * tailMass m a) :
    ∃ p : ℕ, p.Prime ∧ X * (1 + δ * a) < p ∧
      (p : ℝ) < Real.exp u * (X * (1 + δ * (1 - a))) := by
  have hX0pos : 0 < X0 := (Real.exp_pos 38).trans_le hX0
  have hXpos : 0 < X := hX0pos.trans_le hX
  have hbudgetX := normalizedBudget_lt_of_base m hδ.le hu hX0pos hX ha ha2 hgap hs hbudget
  have hbudgetX' := (normalizedBudget_lt_iff m δ a hu hXpos).mp hbudgetX
  have hmargin : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient δ u X * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) <
        psiAverage m δ u X := by
    linarith
  have hcentral := central_positive_of_psi_margin hCosta m hδ.le hδ1 hu.le hu1
    (hX0.trans hX) ha ha2 htail hmargin
  exact prime_of_smoothing hδ hu.le hXpos ha ha2 hcentral

end LeanLab.KadiriLumley2014.Task301

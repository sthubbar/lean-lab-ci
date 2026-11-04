/-
P0059 arXiv 1407.7902v1 page 4 after equation 2.18.
Qualitative decay of the actual absolute zero sum. No effective rate is asserted.
AI wrote this Lean code. CODEX task301. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.Budget301
import LeanLab.KadiriLumley2014.DecompJ336

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory Filter Topology
open Task64 Task92

/-- A single strip zero has a negative exponent of X and hence a vanishing contribution. -/
theorem zeroSummand_tendsto_zero (m : ℕ) (δ u : ℝ)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    Tendsto (fun X : ℝ => zeroSummand m δ u X ρ) atTop (𝓝 0) := by
  have hp := tendsto_rpow_neg_atTop (y := 1 - (ρ : ℂ).re) (by linarith [ρ.property.2.2])
  have he : -(1 - (ρ : ℂ).re) = (ρ : ℂ).re - 1 := by ring
  rw [he] at hp
  simpa only [zeroSummand, mul_zero] using
    hp.const_mul ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u ρ‖)

/-- Dominated convergence makes Sigma tend to zero once it is summable at one positive base.
This implication is CONDITIONAL ON summability at that base. -/
theorem zeroError_tendsto_zero (m : ℕ) (δ u : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (hs : Summable (zeroSummand m δ u X0)) :
    Tendsto (fun X : ℝ => zeroError m δ u X) atTop (𝓝 0) := by
  have hdom : ∀ᶠ X : ℝ in atTop, ∀ ρ, ‖zeroSummand m δ u X ρ‖ ≤ zeroSummand m δ u X0 ρ := by
    filter_upwards [eventually_ge_atTop X0] with X hX
    intro ρ
    rw [Real.norm_eq_abs, abs_of_nonneg (zeroSummand_nonneg m δ u (hX0.le.trans hX) ρ)]
    exact zeroSummand_antitone m δ u hX0 hX ρ
  have h := tendsto_tsum_of_dominated_convergence hs
    (fun ρ => zeroSummand_tendsto_zero m δ u ρ) hdom
  simpa only [zeroError, tsum_zero] using h

/-- The proved zero count supplies the positive base, without an explicit formula input. -/
theorem zeroError_tendsto_zero_small {m : ℕ} (hm : 2 ≤ m) {δ u : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001) :
    Tendsto (fun X : ℝ => zeroError m δ u X) atTop (𝓝 0) :=
  zeroError_tendsto_zero m δ u (Real.exp_pos 38)
    (Task336.lemma2_2_summable hm hδ hδ1 hu hu1 le_rfl)

/-- At a zero endpoint cutoff the complete normalized error tends to zero.
This implication is CONDITIONAL ON summability at a positive base. -/
theorem normalizedBudget_zero_tendsto_zero (m : ℕ) (δ u : ℝ) {X0 : ℝ}
    (hX0 : 0 < X0) (hs : Summable (zeroSummand m δ u X0)) :
    Tendsto (fun X : ℝ => normalizedBudget m δ u X 0) atTop (𝓝 0) := by
  have hz := zeroError_tendsto_zero m δ u hX0 hs
  have hr := (tendsto_const_nhds (x := u / (2 * (Real.exp u - 1)))).div_atTop
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have homega := (tendsto_const_nhds (x := (2.05022 * 10 ^ (-3 : ℤ)) / (Real.exp u - 1))).div_atTop
    tendsto_sqrt_atTop
  have h := (hz.add hr).add homega
  simpa only [normalizedBudget, tailMass, sub_zero, intervalIntegral.integral_same,
    add_zero, mul_zero, zero_div, zero_mul, div_div] using h

/-- A normalized certificate exists at sufficiently large X for a zero endpoint cutoff.
This implication is CONDITIONAL ON summability and supplies no explicit threshold. -/
theorem exists_normalizedBudget_lt (m : ℕ) {δ u X0 : ℝ}
    (hδ : 0 ≤ δ) (hX0 : 0 < X0) (hs : Summable (zeroSummand m δ u X0)) (B : ℝ) :
    ∃ X : ℝ, B ≤ X ∧ normalizedBudget m δ u X 0 < 1 + δ / 2 := by
  have hlim := normalizedBudget_zero_tendsto_zero m δ u hX0 hs
  have hpos : (0 : ℝ) < 1 + δ / 2 := by linarith
  have hlt : ∀ᶠ X : ℝ in atTop, normalizedBudget m δ u X 0 < 1 + δ / 2 :=
    hlim.eventually (eventually_lt_nhds hpos)
  exact ((eventually_ge_atTop B).and hlt).exists

end LeanLab.KadiriLumley2014.Task301

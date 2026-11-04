/-
P0059 arXiv 1407.7902v1 page 4 after equation 2.18 and page 5 equation 2.20.
Qualitative limiting endpoint budget. No effective threshold is asserted.
AI wrote this Lean code. CODEX task301. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroLimit301
import LeanLab.KadiriLumley2014.WeightMass

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory Filter Topology
open Task64 Task92

/-- The logarithmic endpoint ratio tends to one for positive u and nonnegative delta. -/
theorem tail_ratio_tendsto_one {u δ : ℝ} (hu : 0 < u) (hδ : 0 ≤ δ) :
    Tendsto (fun X : ℝ =>
      Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) atTop (𝓝 1) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hd : 0 < 1 + δ := by linarith
  have hden : Tendsto (fun X : ℝ => Real.log X + Real.log (Real.exp u - 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop _ Real.tendsto_log_atTop
  have hr := (tendsto_const_nhds (x := u + Real.log (1 + δ) - Real.log (Real.exp u - 1))).div_atTop hden
  have h : Tendsto (fun X : ℝ =>
      1 + (u + Real.log (1 + δ) - Real.log (Real.exp u - 1)) /
        (Real.log X + Real.log (Real.exp u - 1))) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hr
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hden.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hD
  rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero u) hX.ne') hd.ne',
    Real.log_mul (Real.exp_ne_zero u) hX.ne', Real.log_exp,
    Real.log_mul hX.ne' he.ne']
  field_simp
  ring

/-- The complete normalized budget tends to its endpoint mass coefficient.
This implication is CONDITIONAL ON summability at a positive base. -/
theorem normalizedBudget_tendsto_tail (m : ℕ) {δ u X0 a : ℝ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hX0 : 0 < X0) (hs : Summable (zeroSummand m δ u X0)) :
    Tendsto (fun X : ℝ => normalizedBudget m δ u X a) atTop
      (𝓝 (2 * (1 + δ) * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t))) := by
  have hz := normalizedBudget_zero_tendsto_zero m δ u hX0 hs
  have ht := (tail_ratio_tendsto_one hu hδ).const_mul
    (2 * (1 + δ) * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t))
  have h := hz.add ht
  simpa only [normalizedBudget, tailMass, sub_zero, intervalIntegral.integral_same,
    add_zero, mul_zero, zero_div, zero_mul, zero_add, mul_one] using h

/-- Any strict limiting endpoint margin gives an eventual normalized certificate.
This implication is CONDITIONAL ON summability and the limiting mass margin. -/
theorem exists_normalizedBudget_lt_of_tail (m : ℕ) {δ u X0 a : ℝ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hX0 : 0 < X0) (hs : Summable (zeroSummand m δ u X0))
    (htail : 2 * (1 + δ) * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) < 1 + δ / 2)
    (B : ℝ) :
    ∃ X : ℝ, B ≤ X ∧ normalizedBudget m δ u X a < 1 + δ / 2 := by
  have hlim := normalizedBudget_tendsto_tail m hδ hu hX0 hs (a := a)
  have hlt := hlim.eventually (eventually_lt_nhds htail)
  exact ((eventually_ge_atTop B).and hlt).exists

/-- A positive endpoint cutoff has a strict limiting margin for the quadratic weight. -/
theorem quadratic_weight_tail_margin {δ : ℝ} (hδ : 0 ≤ δ) :
    2 * (1 + δ) * tailMass 2 (1 / 8) / (∫ t in (0 : ℝ)..1, weight 2 t) < 1 + δ / 2 := by
  have hb := tailMass_le_endpoint 2 (a := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  norm_num at hb
  have hmass : (∫ t in (0 : ℝ)..1, weight 2 t) = 8 / 15 := by
    norm_num [weight_mass, Nat.factorial]
  rw [hmass]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8 / 15)).mpr
  have hmul := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 2 * (1 + δ))
  nlinarith

/-- A concrete positive cutoff gives qualitative certificates in the paper's parameter domain.
There is no cited analytic input and no effective bound on X. -/
theorem exists_positive_cutoff_certificate {δ u : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001) (B : ℝ) :
    ∃ X : ℝ, B ≤ X ∧ normalizedBudget 2 δ u X (1 / 8) < 1 + δ / 2 := by
  exact exists_normalizedBudget_lt_of_tail 2 hδ.le hu (Real.exp_pos 38)
    (Task336.lemma2_2_summable (by norm_num) hδ hδ1 hu hu1 le_rfl)
    (quadratic_weight_tail_margin hδ.le) B

end LeanLab.KadiriLumley2014.Task301

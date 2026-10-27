import LeanLab.GoldbachAverage.WeightedSquare124

/-!
The short interval Cauchy Schwarz estimate in P0051 page 11.
This controls the last pointwise term before the change in integration order.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.WeightedCauchy124
open MeasureTheory Filter
open FloorVariance82 WeightedPrefixBound82 WeightedIncrement124 WeightedSquare124

/-- The weighted absolute R function is square integrable on a nonnegative short interval.
Source: P0051 page 11, the Cauchy Schwarz step for the double integral. -/
theorem weighted_R_memLp_two (N : ℕ) (hN : 1 ≤ N) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) :
    MemLp (fun u => |psiFloorError u| * Real.exp (-u / N)) 2
      (volume.restrict (Set.Ioc x (x + h))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : Set.Ioc x (x + h) ⊆ Set.Ioc 0 (x + h) := by
    intro u hu
    exact ⟨lt_of_le_of_lt hx hu.1, hu.2⟩
  have hR : MemLp psiFloorError 2 (volume.restrict (Set.Ioc x (x + h))) :=
    MemLp.mono_measure (Measure.restrict_mono hsub le_rfl)
      (R_memLp (by linarith : 0 ≤ x + h) 2)
  have hRa : MemLp (fun u => |psiFloorError u|) 2
      (volume.restrict (Set.Ioc x (x + h))) := by
    simpa only [Real.norm_eq_abs] using hR.norm
  refine hRa.mono' ((measurable_psiFloorError.abs.mul (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 ≤ u := hx.trans hu.1.le
  have he : Real.exp (-u / N) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa only [neg_div] using neg_nonpos.mpr (div_nonneg hu0 hN0.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg (psiFloorError u))

/-- LEAF. P0051 page 11, the weighted short integral squared is at most h times
its weighted square integral. This precedes the change in order of integration. -/
theorem weighted_R_short_integral_sq (N : ℕ) (hN : 1 ≤ N) {x h : ℝ}
    (hx : 0 ≤ x) (hh : 0 ≤ h) :
    (∫ u in x..(x + h), |psiFloorError u| * Real.exp (-u / N)) ^ 2 ≤
      h * ∫ u in x..(x + h), psiFloorError u ^ 2 * Real.exp (-2 * u / N) := by
  have hab : x ≤ x + h := by linarith
  let μ : Measure ℝ := volume.restrict (Set.Ioc x (x + h))
  let g : ℝ → ℝ := fun u => |psiFloorError u| * Real.exp (-u / N)
  have hg : MemLp g (ENNReal.ofReal 2) μ := by
    simpa [g, μ] using weighted_R_memLp_two N hN hx hh
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    exact MemLp.of_bound measurable_const.aestronglyMeasurable 1
      (Eventually.of_forall fun _ => by simp)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall fun u => by dsimp [g]; positivity)
    (Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hg hone
  norm_num only [Real.rpow_two, one_pow, mul_one] at hHolder
  have hsq (u : ℝ) : g u ^ 2 = psiFloorError u ^ 2 * Real.exp (-2 * u / N) := by
    dsimp [g]
    rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
    congr 2
    norm_num
    ring
  have hg2 : (∫ u, g u ^ 2 ∂μ) =
      ∫ u in x..(x + h), psiFloorError u ^ 2 * Real.exp (-2 * u / N) := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_congr_ae (Eventually.of_forall hsq)
  have hOneInt : (∫ _u, (1 : ℝ) ∂μ) = h := by
    change (∫ _u in Set.Ioc x (x + h), (1 : ℝ)) = h
    rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hg2, hOneInt, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hHolder
  have hcs : (∫ u in x..(x + h), g u) ≤
      Real.sqrt (∫ u in x..(x + h), psiFloorError u ^ 2 * Real.exp (-2 * u / N)) *
        Real.sqrt h := by
    simpa only [intervalIntegral.integral_of_le hab, μ] using hHolder
  have hg0 : 0 ≤ ∫ u in x..(x + h), g u :=
    intervalIntegral.integral_nonneg hab (fun _ _ => by dsimp [g]; positivity)
  have hsq0 : 0 ≤ ∫ u in x..(x + h), psiFloorError u ^ 2 * Real.exp (-2 * u / N) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => by positivity)
  have hs := pow_le_pow_left₀ hg0 hcs 2
  rw [mul_pow, Real.sq_sqrt hsq0, Real.sq_sqrt hh] at hs
  simpa only [g, mul_comm] using hs

end LeanLab.GoldbachAverage.WeightedCauchy124

/-
P0059 page 7 display 2.48 and source 4, arXiv 1310.6374 page 9 Lemma 2.7.
Finite partial summation proves the density reciprocal-power estimate.
All zero inputs remain explicit hypotheses.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroFinite399
import LeanLab.KadiriLumley2014.DensityPrimitive399

namespace LeanLab.KadiriLumley2014.Task399

open Real Set MeasureTheory
open Task259

/-- A finite common zero cutoff makes the density count times any interval-integrable function integrable. -/
theorem densityCount_mul_integrable {H V σ : ℝ} (hHV : H ≤ V)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume H V) :
    IntervalIntegrable (fun t => densityCount σ t * f t) volume H V := by
  classical
  have hi : IntervalIntegrable (fun t => (∑ ρ ∈ positiveZerosBelow V,
      if σ < (ρ : ℂ).re ∧ (ρ : ℂ).im < t then
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) * f t) volume H V := by
    have hfi : ∀ ρ ∈ positiveZerosBelow V, IntervalIntegrable
        (fun t => (if σ < (ρ : ℂ).re ∧ (ρ : ℂ).im < t then
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) else 0) * f t) volume H V := by
      intro ρ _
      by_cases hr : σ < (ρ : ℂ).re
      · simpa only [hr, true_and, ite_mul, zero_mul] using
          after_cut_integrable (γ := (ρ : ℂ).im)
            (hf.const_mul (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ))
      · simp only [hr, false_and, ite_false, zero_mul]
        exact intervalIntegrable_const
    convert IntervalIntegrable.sum (positiveZerosBelow V) hfi using 1
    ext t
    simp only [Finset.sum_apply, Finset.sum_mul]
  apply hi.congr
  intro t ht
  have htV : t ≤ V := by
    rw [uIoc_of_le hHV] at ht
    exact ht.2
  dsimp only
  rw [densityCount_eq_finite htV]

/-- The derivative of the reciprocal ordinate power used in cited display 2.25. -/
theorem reciprocal_power_derivative (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 1 / t ^ (m + 1))
      (-((m : ℝ) + 1) / t ^ (m + 2)) t := by
  have h := ((hasDerivAt_id t).pow (m + 1)).inv (pow_ne_zero _ ht.ne')
  convert h using 1
  · ext x
    simp
  · simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [pow_succ]
    field_simp

/-- The finite density reciprocal-power sum has a uniform primitive bound.
CONDITIONAL ON verified height and the displayed density envelope. -/
theorem density_power_partial_bound {m : ℕ} (hm : 0 < m)
    {H V σ c1 c2 c3 : ℝ} (hH : 0 < H) (hHV : H ≤ V)
    (hσ : 1 / 2 < σ) (hRH : VerifiedHeight H)
    (hDensity : ∀ t ∈ Icc H V, densityCount σ t ≤ c1 * t + c2 * Real.log t + c3)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    positiveZeroSum (fun ρ => if σ < ρ.re ∧ ρ.im < V then 1 / ρ.im ^ (m + 1) else 0) ≤
      densityPrimitive m c1 c2 c3 H := by
  have hV : 0 < V := hH.trans_le hHV
  have hc : ContinuousOn (fun t : ℝ => ((m : ℝ) + 1) / t ^ (m + 2)) (Icc H V) := by
    fun_prop (disch := intro t ht; positivity [hH.trans_le ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => ((m : ℝ) + 1) / t ^ (m + 2)) volume H V :=
    hc.intervalIntegrable_of_Icc hHV
  have hneg : IntervalIntegrable (fun t : ℝ => -((m : ℝ) + 1) / t ^ (m + 2)) volume H V := by
    convert hi.neg using 1
    ext t
    simp only [Pi.neg_apply, neg_div]
  have hN := densityCount_mul_integrable (σ := σ) hHV hi
  have hB : IntervalIntegrable (fun t : ℝ => (c1 * t + c2 * Real.log t + c3) *
      (((m : ℝ) + 1) / t ^ (m + 2))) volume H V := by
    have hcont : ContinuousOn (fun t : ℝ => (c1 * t + c2 * Real.log t + c3) *
        (((m : ℝ) + 1) / t ^ (m + 2))) (Icc H V) := by
      fun_prop (disch := intro t ht; positivity [hH.trans_le ht.1])
    exact hcont.intervalIntegrable_of_Icc hHV
  have hbound : (∫ t in H..V, densityCount σ t * (((m : ℝ) + 1) / t ^ (m + 2))) ≤
      ∫ t in H..V, (c1 * t + c2 * Real.log t + c3) * (((m : ℝ) + 1) / t ^ (m + 2)) := by
    apply intervalIntegral.integral_mono_on hHV hN hB
    intro t ht
    exact mul_le_mul_of_nonneg_right (hDensity t ht) (by positivity [hH.trans_le ht.1])
  have heval : (∫ t in H..V, (c1 * t + c2 * Real.log t + c3) *
      (((m : ℝ) + 1) / t ^ (m + 2))) =
      densityPrimitive m c1 c2 c3 H - densityPrimitive m c1 c2 c3 V := by
    convert integral_density_power hm c1 c2 c3 hH hHV using 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  have hmain := density_partial_summation hHV hσ hRH
    (fun t ht => reciprocal_power_derivative m (hH.trans_le ht.1)) hneg
  have hrewrite : (∫ t in H..V, densityCount σ t * (-((m : ℝ) + 1) / t ^ (m + 2))) =
      -(∫ t in H..V, densityCount σ t * (((m : ℝ) + 1) / t ^ (m + 2))) := by
    simp only [neg_div, mul_neg, intervalIntegral.integral_neg]
  rw [hrewrite] at hmain
  have hend : 1 / V ^ (m + 1) * densityCount σ V ≤
      (c1 * V + c2 * Real.log V + c3) / V ^ (m + 1) := by
    have h := mul_le_mul_of_nonneg_left (hDensity V ⟨hHV, le_rfl⟩)
      (by positivity : 0 ≤ 1 / V ^ (m + 1))
    simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using h
  have htail1 : 0 ≤ c1 / ((m : ℝ) * V ^ m) := by positivity
  have htail2 : 0 ≤ c2 / (((m : ℝ) + 1) * V ^ (m + 1)) := by positivity
  rw [heval] at hbound
  unfold densityPrimitive
  rw [hmain]
  dsimp only [densityPrimitive] at hbound
  linarith

/-- The full density reciprocal-power estimate follows from finite partial sums.
CONDITIONAL ON verified height and the displayed global density envelope. -/
theorem density_power_tail_bound {m : ℕ} (hm : 0 < m)
    {H σ c1 c2 c3 : ℝ} (hH : 0 < H)
    (hσ : 1 / 2 < σ) (hRH : VerifiedHeight H)
    (hDensity : ∀ t, H ≤ t → densityCount σ t ≤ c1 * t + c2 * Real.log t + c3)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    positiveZeroSum (fun ρ => if H < ρ.im ∧ σ < ρ.re then 1 / ρ.im ^ (m + 1) else 0) ≤
      densityPrimitive m c1 c2 c3 H := by
  classical
  have hB : 0 ≤ c1 * H + c2 * Real.log H + c3 := by
    have hN : 0 ≤ densityCount σ H := by
      unfold densityCount positiveZeroSum
      apply tsum_nonneg
      intro ρ
      split_ifs <;> positivity
    exact hN.trans (hDensity H le_rfl)
  have hF : 0 ≤ densityPrimitive m c1 c2 c3 H := by
    unfold densityPrimitive
    positivity
  unfold positiveZeroSum
  apply tsum_le_of_sum_le' hF
  intro s
  let V : ℝ := H + (∑ ρ ∈ s, |(ρ : ℂ).im|) + 1
  have hHV : H ≤ V := by
    dsimp [V]
    linarith [Finset.sum_nonneg (fun ρ (_ : ρ ∈ s) => abs_nonneg (ρ : ℂ).im)]
  have hmemV : ∀ ρ ∈ s, (ρ : ℂ).im < V := by
    intro ρ hρ
    have hle := Finset.single_le_sum (fun i (_ : i ∈ s) => abs_nonneg (i : ℂ).im) hρ
    have habs := le_abs_self (ρ : ℂ).im
    dsimp [V]
    linarith
  let g := fun ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} =>
    if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
      (if σ < (ρ : ℂ).re ∧ (ρ : ℂ).im < V then 1 / (ρ : ℂ).im ^ (m + 1) else 0) else 0
  have hg : Summable g := summable_bounded_positive_zero_family V
    (fun ρ => if σ < ρ.re ∧ ρ.im < V then 1 / ρ.im ^ (m + 1) else 0)
    (fun ρ hρ => ite_eq_right (by intro h; linarith [h.2]))
  have hgn : ∀ ρ, 0 ≤ g ρ := by
    intro ρ
    dsimp [g]
    split_ifs with hp h
    · positivity
    · simp
    · rfl
  calc
    _ ≤ ∑ ρ ∈ s, g ρ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      dsimp [g]
      by_cases hp : 0 < (ρ : ℂ).im
      · simp only [ite_eq_left hp]
        by_cases h : H < (ρ : ℂ).im ∧ σ < (ρ : ℂ).re
        · simp [h, hmemV ρ hρ]
        · simp only [ite_eq_right h, mul_zero]
          exact (hgn ρ).trans_eq (by simp [g, hp])
      · simp [hp]
    _ ≤ ∑' ρ, g ρ := hg.sum_le_tsum s (fun ρ _ => hgn ρ)
    _ ≤ _ := density_power_partial_bound hm hH hHV hσ hRH
      (fun t ht => hDensity t ht.1) hc1 hc2

end LeanLab.KadiriLumley2014.Task399

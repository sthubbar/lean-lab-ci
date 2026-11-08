/-
Unscaled integrability and the exact integer region split.
Source: P0029 page 26 display 7.4 and page 27 display 7.8.
No decay estimate is needed for these identities at fixed positive scales.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.IntegerArcs461

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped FourierTransform

/-- The finite continuous rational model is bounded at every fixed denominator cutoff.
This uses Fourier boundedness and does not require a lower bound on the scales. -/
theorem continuousModel_bound461 {G : ℝ → ℝ} (hG : IsMajorWeight G) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, ∀ T : ℕ → ℝ, ∀ α : ℝ,
      ‖continuousModel405 G R T α‖ ≤ C * (⌊R⌋₊ : ℝ) ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := fourier_decay hG.supp hG.smooth 0
  refine ⟨C, hC, ?_⟩
  intro R T α
  rw [continuousModel405, ← sum_reducedPairs]
  have hterm : ∀ p ∈ reducedPairs ⌊R⌋₊,
      ‖centeredFourier405 G (T p.1) (α - p.2 / p.1)‖ ≤ C := by
    intro p hp
    simpa only [centeredFourier405, neg_zero, Real.rpow_zero, mul_one] using
      hb (-(T p.1) * ((α - p.2 / p.1) - round (α - p.2 / p.1)))
  have hh := norm_sum_le_card_mul _ _ hterm
  have hc : ((reducedPairs ⌊R⌋₊).card : ℝ) ≤ (⌊R⌋₊ : ℝ) ^ 2 := by
    exact_mod_cast reducedPairs_card_le ⌊R⌋₊
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hc hC.le])

/-- The continuous tail integral and its integrability hold without the separation scale.
This is an identity at fixed positive X and eta, not a uniform family bound. -/
theorem continuousTail_unscaled461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η) :
    IntervalIntegrable
      (fun α => {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
        (fun α => Sphi ϕ N α ^ 2 *
          (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
            continuousModel405 G ((X : ℝ) ^ ϑ)
              (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α)
      volume 0 1 ∧
    continuousTail405 ϕ G X N ϑ η =
      ∫ α in (0 : ℝ)..1, {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
        (fun α => Sphi ϕ N α ^ 2 *
          (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
            continuousModel405 G ((X : ℝ) ^ ϑ)
              (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α := by
  classical
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  let s : Set ℝ := {α | MajorArc X R α}
  have hs : MeasurableSet s := measurableSet_majorArc84 X R
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hXp ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    dsimp [T]
    positivity
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hMb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left M 0)
  obtain ⟨C, hC, hb⟩ := continuousModel_bound461 hG
  have hmodel := smoothed_multiplier_memLp261 (le_max_right M 0) hMb
    (measurable_continuousModel405 hG R T)
    (by positivity : 0 ≤ C * (⌊R⌋₊ : ℝ) ^ 2) (hb R T) N
  have hnear := nearSquare_memLp328 ϕ hG.supp hXp hRp hη N
  have hfull : MemLp (fun α => Sphi ϕ N α ^ 2 * bRhat G R T α)
      2 (volume.restrict (Set.Ioc 0 1)) := by
    simpa [arcSquare328] using arcSquare_memLp328 ϕ
      (continuous_bRhat hG.supp hG.even R T hT) MeasurableSet.univ N
  have hint (u v : ℝ → ℂ)
      (hu : MemLp (fun α => Sphi ϕ N α ^ 2 * u α) 2 (volume.restrict (Set.Ioc 0 1)))
      (hv : MemLp (fun α => Sphi ϕ N α ^ 2 * v α) 2 (volume.restrict (Set.Ioc 0 1))) :
      IntervalIntegrable
        (fun α => s.indicator (fun α => Sphi ϕ N α ^ 2 * (u α - v α) * ee (-(N * α))) α)
        volume 0 1 := by
    have hm := (hu.sub hv).indicator hs.nullMeasurableSet
    have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hm.integrable (by norm_num : (1 : ENNReal) ≤ 2))
    have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
      ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
    convert hi.mul_continuousOn he.continuousOn using 1
    funext α
    by_cases ha : α ∈ s <;> simp [Set.indicator, ha, mul_sub]
  have hi := hint (nearTransform328 G X R η) (continuousModel405 G R T) hnear hmodel
  refine ⟨hi, ?_⟩
  have ht := hint (nearTransform328 G X R η) (bRhat G R T) hnear hfull
  have ha := hint (continuousModel405 G R T) (bRhat G R T) hmodel hfull
  rw [continuousTail405, majorTail_eq_integral328 ϕ hG hX N ϑ hη, aliasCoefficient405,
    ← intervalIntegral.integral_sub ht ha]
  apply intervalIntegral.integral_congr
  intro α hα
  dsimp only [s, R, T]
  by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
  · simp only [Set.indicator, Set.mem_setOf_eq, hm, ite_true]
    ring
  · simp only [Set.indicator, Set.mem_setOf_eq, hm, ite_false, sub_self]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.continuousModel_bound461
#print axioms LeanLab.BhowmikGrimmelt2026.continuousTail_unscaled461

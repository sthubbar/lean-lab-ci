/-
Supply for the weighted minor coefficient in P0029 page 27, display 7.8.
Remove the full rational sum Poisson aliases with the proved arbitrary power bound.
The centered continuous multiplier estimate remains OPEN with logarithm power five.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp405a
import LeanLab.BhowmikGrimmelt2026.Decomp328b

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The weighted minor coefficient after subtracting its full Poisson alias part. -/
noncomputable def continuousWeighted405 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  minorWeighted328 ϕ G X N ϑ η -
    aliasOn405 ϕ G X N ϑ η {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}

/-- The minor arc Poisson alias family fits the printed power budget with logarithm one.
No logarithm power five prime estimate is used. -/
theorem minor_alias_family405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖aliasOn405 ϕ G X N ϑ η {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}‖ ^ 2 ≤
          C * (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 * Real.log X := by
  obtain ⟨C, hC, hf⟩ := alias_on_family405 hϕ hG ϑ hϑ (1 / 5) (by norm_num)
  refine ⟨C, hC, fun X hX η hη hscale => ?_⟩
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hp : ((X : ℝ) ^ (-(1 / 5) : ℝ)) ^ 2 = (X : ℝ) ^ (-(2 / 5) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]
    norm_num
  simpa only [hp, Set.compl_setOf] using hf X hX η hη hscale _ (measurableSet_majorArc84 _ _).compl

/-- The remaining weighted coefficient is exactly negative the centered continuous
rational multiplier on the minor arcs. This equality justifies the smaller leaf. -/
theorem continuousWeighted_eq_integral405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    continuousWeighted405 ϕ G X N ϑ η =
      -(∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
        (fun α => Sphi ϕ N α ^ 2 *
          continuousModel405 G ((X : ℝ) ^ ϑ)
            (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))) α) := by
  classical
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  let s : Set ℝ := {α | ¬ MajorArc X R α}
  have hs : MeasurableSet s := (measurableSet_majorArc84 X R).compl
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hxp ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    dsimp [T]
    positivity
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  let F : ℝ → ℂ := s.indicator (fun α =>
    Sphi ϕ N α ^ 2 * bRhat G R T α * ee (-(N * α)))
  let H : ℝ → ℂ := s.indicator (fun α => Sphi ϕ N α ^ 2 *
    (continuousModel405 G R T α - bRhat G R T α) * ee (-(N * α)))
  have hFc : Continuous (fun α => Sphi ϕ N α ^ 2 * bRhat G R T α * ee (-(N * α))) :=
    (((continuous_Sphi ϕ N).pow 2).mul
      (continuous_bRhat hG.supp hG.even R T hT)).mul he
  have hFi : IntervalIntegrable F volume 0 1 :=
    ⟨(hFc.intervalIntegrable 0 1).1.indicator hs,
     (hFc.intervalIntegrable 0 1).2.indicator hs⟩
  obtain ⟨D, hD, hbound⟩ := alias_multiplier405 hG ϑ hϑ
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hMb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left _ _)
  have hm : Measurable (fun α => continuousModel405 G R T α - bRhat G R T α) :=
    (measurable_continuousModel405 hG R T).sub
      (continuous_bRhat hG.supp hG.even R T hT).measurable
  have ha := smoothed_multiplier_memLp261 (le_max_right M 0) hMb hm
    (by positivity : 0 ≤ D * η ^ 2) (fun α => by
      rw [norm_sub_rev]
      exact hbound X hX η hη hscale α) N
  have hai : IntervalIntegrable (fun α => Sphi ϕ N α ^ 2 *
      (continuousModel405 G R T α - bRhat G R T α) * ee (-(N * α))) volume 0 1 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (ha.integrable (by norm_num : (1 : ENNReal) ≤ 2))).mul_continuousOn he.continuousOn
  have hHi : IntervalIntegrable H volume 0 1 := ⟨hai.1.indicator hs, hai.2.indicator hs⟩
  change minorWeighted328 ϕ G X N ϑ η - (∫ α in (0 : ℝ)..1, H α) = _
  rw [minorWeighted_eq_integral328 hG ϕ hX N ϑ hη]
  change -(∫ α in (0 : ℝ)..1, F α) - (∫ α in (0 : ℝ)..1, H α) = _
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub (f := fun α => -F α) (g := fun α => H α) hFi.neg hHi,
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases hh : α ∈ s
  · have hh' : ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hh
    simp [F, H, s, R, T, Set.indicator, hh']
    ring
  · have hh' : ¬ ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hh
    simp [F, H, s, R, T, Set.indicator, hh']

/-- LEAF. P0029 page 27, the bounded multiplier step in the minor part of 7.8.
OPEN centered continuous rational multiplier estimate with logarithm power five.
The full rational sum Poisson aliases are absent and have a separate proved bound.
The exact remaining integral is given by continuousWeighted_eq_integral405. -/
theorem continuous_weighted_family405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖continuousWeighted405 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- Exact minor_weighted_family328 statement assembled from the continuous leaf and
proved aliases. CONDITIONAL ON continuous_weighted_family405. -/
theorem minor_weighted_supply405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, hc⟩ := continuous_weighted_family405 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, ha⟩ := minor_alias_family405 hϕ hG ϑ hϑ
  refine ⟨2 * (C₁ + 16 * C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ X by exact_mod_cast hX)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by linarith [Real.log_two_gt_d9]
  have hlog5 : Real.log (X : ℝ) ≤ 16 * Real.log X ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
    have hh := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ Real.log (X : ℝ))
    norm_num at hh
    nlinarith only [hh]
  have halias := ha X hX η hη hscale
  have hcont := hc X hX η hη hη1 hscale
  have hsplit := coefficient_split328 (Finset.Icc 1 X)
    (fun N => minorWeighted328 ϕ G X N ϑ η)
    (fun N => aliasOn405 ϕ G X N ϑ η {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α})
  change _ ≤ 2 * ((_ : ℝ) + ∑ N ∈ Finset.Icc 1 X,
    ‖continuousWeighted405 ϕ G X N ϑ η‖ ^ 2) at hsplit
  have ha5 : (∑ N ∈ Finset.Icc 1 X,
      ‖aliasOn405 ϕ G X N ϑ η {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}‖ ^ 2) ≤
      16 * C₂ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
        (X : ℝ) ^ 3 * Real.log X ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left hlog5
      (by positivity : 0 ≤ C₂ * (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3)
    have h2 := mul_nonneg
      (by positivity : 0 ≤ 16 * C₂ * ((X : ℝ) ^ ϑ)⁻¹ * (X : ℝ) ^ 3)
      (by positivity : 0 ≤ Real.log (X : ℝ) ^ 5)
    nlinarith only [halias, h1, h2]
  nlinarith only [hsplit, hcont, ha5]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minor_alias_family405
#print axioms LeanLab.BhowmikGrimmelt2026.continuousWeighted_eq_integral405
#print axioms LeanLab.BhowmikGrimmelt2026.continuous_weighted_family405
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_supply405

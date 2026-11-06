/-
Supply for the off rational major family on P0029 pages 26 and 27.
Separate the full rational sum Poisson aliases from its centered continuous model.
The aliases have a clean bound. The central minus continuous remainder stays OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp328a
import LeanLab.BhowmikGrimmelt2026.FiniteSum

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped FourierTransform

/-- The zero Poisson translate after choosing a nearest integer representative.
Page 26, the Poisson formula before display 7.6. -/
noncomputable def centeredFourier405 (G : ℝ → ℝ) (T β : ℝ) : ℂ :=
  𝓕 (fun x : ℝ => (G x : ℂ)) (-T * (β - round β))

/-- The centered continuous rational sum from the zero Poisson translates in 7.4. -/
noncomputable def continuousModel405 (G : ℝ → ℝ) (R : ℝ) (T : ℕ → ℝ) (α : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊R⌋₊,
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      centeredFourier405 G (T q) (α - a / q)

/-- Centering does not affect the discrete transform, so the zero translate error decays. -/
theorem centeredFourier_error405 {G : ℝ → ℝ} (hG : IsMajorWeight G) (A : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ T β : ℝ, 1 ≤ T →
      ‖GThat G T β - centeredFourier405 G T β‖ ≤ D * T ^ (-A) := by
  obtain ⟨D, hD, hb⟩ := GThat_poisson_error hG.supp hG.smooth A
  refine ⟨D, hD, fun T β hT => ?_⟩
  simpa only [centeredFourier405, GThat_center] using
    hb T (β - round β) hT (abs_sub_round β)

/-- The centered continuous transform is measurable despite the representative jumps. -/
theorem measurable_centeredFourier405 {G : ℝ → ℝ} (hG : IsMajorWeight G) (T : ℝ) :
    Measurable (centeredFourier405 G T) := by
  have hr : Measurable (fun β : ℝ => round β) := by
    simp_rw [round_eq]
    exact (measurable_id.add_const (1 / 2 : ℝ)).floor
  have hc : Measurable (fun β : ℝ => ((round β : ℤ) : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hr
  have hf : Continuous (𝓕 (fun x : ℝ => (G x : ℂ))) := by
    exact (𝓕 (weightSchwartz hG.supp hG.smooth)).continuous
  exact hf.measurable.comp (measurable_const.mul (measurable_id.sub hc))

/-- The finite centered continuous rational model is measurable. -/
theorem measurable_continuousModel405 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (R : ℝ) (T : ℕ → ℝ) : Measurable (continuousModel405 G R T) := by
  classical
  unfold continuousModel405
  apply Finset.measurable_sum
  intro q hq
  apply Finset.measurable_sum
  intro a ha
  exact (measurable_centeredFourier405 hG (T q)).comp (measurable_id.sub_const _)

/-- The sum of the Poisson alias errors is bounded by the reduced pair count.
The lower scale is independent of the rational numerator and denominator. -/
theorem continuousModel_error405 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ R B : ℝ, 0 ≤ R → 1 ≤ B → ∀ T : ℕ → ℝ,
      (∀ q ∈ Finset.Icc 1 ⌊R⌋₊, B ≤ T q) → ∀ α : ℝ,
      ‖bRhat G R T α - continuousModel405 G R T α‖ ≤ D * R ^ 2 * B ^ (-A) := by
  classical
  obtain ⟨D, hD, hb⟩ := centeredFourier_error405 hG A
  refine ⟨D, hD, fun R B hR hB T hT α => ?_⟩
  have hTpos : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    linarith [hT q hq]
  rw [bRhat_eq hG.supp hG.even R T hTpos, continuousModel405,
    ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [← sum_reducedPairs]
  have hterm : ∀ p ∈ reducedPairs ⌊R⌋₊,
      ‖GThat G (T p.1) (α - p.2 / p.1) -
        centeredFourier405 G (T p.1) (α - p.2 / p.1)‖ ≤ D * B ^ (-A) := by
    intro p hp
    have hm := (mem_reducedPairs _ _).mp hp
    have hq : p.1 ∈ Finset.Icc 1 ⌊R⌋₊ := Finset.mem_Icc.mpr ⟨hm.1, hm.2.1⟩
    exact (hb _ _ (hB.trans (hT _ hq))).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) (hT _ hq) (by linarith)) hD.le)
  apply (norm_sum_le_card_mul _ _ hterm).trans
  have hcard : ((reducedPairs ⌊R⌋₊).card : ℝ) ≤ R ^ 2 := by
    calc
      _ ≤ (⌊R⌋₊ : ℝ) ^ 2 := by exact_mod_cast reducedPairs_card_le ⌊R⌋₊
      _ ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) (Nat.floor_le hR) 2
  nlinarith [mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ D * B ^ (-A))]

/-- Full scale decay pays both the rational pair count and the desired eta squared.
This concerns only the Poisson aliases, not the off rational central translates. -/
theorem alias_scale405 {x ϑ η : ℝ} (hx : 1 ≤ x) (hϑ : 0 < ϑ)
    (hη : 0 < η) (hscale : 10 * (x ^ ϑ) ^ 2 ≤ η * x) :
    (x ^ ϑ) ^ 2 * (x ^ ϑ) ^ (-(2 + 2 / ϑ)) ≤ η ^ 2 := by
  have hxp : 0 < x := by linarith
  have hRp : 0 < x ^ ϑ := Real.rpow_pos_of_pos hxp ϑ
  have hpow : (x ^ ϑ) ^ 2 * (x ^ ϑ) ^ (-(2 + 2 / ϑ)) =
      (x ^ ϑ) ^ (-(2 / ϑ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hRp]
    congr 1
    ring
  rw [hpow]
  have h := central_scale_tail328 hx hϑ hη (by norm_num : (1 : ℝ) ≤ 1) hscale
  have hRT : x ^ ϑ ≤ η * x * 1 / x ^ ϑ := by
    apply (le_div_iff₀ hRp).mpr
    nlinarith [sq_nonneg (x ^ ϑ)]
  have hinv : 1 / x ≤ η := by
    apply (div_le_iff₀ hxp).mpr
    nlinarith [Real.one_le_rpow hx hϑ.le, sq_nonneg (x ^ ϑ - 1)]
  have he : ϑ * (-(2 / ϑ)) = -(2 : ℝ) := by field_simp <;> ring
  rw [← Real.rpow_mul hxp.le, he, Real.rpow_neg hxp.le, Real.rpow_two]
  simpa [one_div, inv_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / x) hinv 2

/-- The complete alias multiplier is uniformly of order eta squared.
Page 26, sum the Poisson errors before estimating distinct rational centers. -/
theorem alias_multiplier405 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ α : ℝ,
      ‖bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
        continuousModel405 G ((X : ℝ) ^ ϑ)
          (fun q => η * X * q / (X : ℝ) ^ ϑ) α‖ ≤ D * η ^ 2 := by
  have hA : 0 ≤ 2 + 2 / ϑ := by positivity
  obtain ⟨D, hD, hb⟩ := continuousModel_error405 hG hA
  refine ⟨D, hD, fun X hX η hη hscale α => ?_⟩
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hx1 hϑ.le
  have hRp : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hxp ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊,
      (X : ℝ) ^ ϑ ≤ η * X * q / (X : ℝ) ^ ϑ := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    apply (le_div_iff₀ hRp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq1 (by positivity : 0 ≤ η * X),
      sq_nonneg ((X : ℝ) ^ ϑ)]
  exact (hb _ _ hRp.le hR1 _ hT α).trans (by
    have hh := mul_le_mul_of_nonneg_left (alias_scale405 hx1 hϑ hη hscale) hD.le
    nlinarith only [hh])

/-- The major arc coefficient of the continuous model minus the discrete transform. -/
noncomputable def aliasCoefficient405 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
    (fun α => Sphi ϕ N α ^ 2 *
      (continuousModel405 G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
        bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
      ee (-(N * α))) α

/-- The remaining off rational coefficient after removing the Poisson aliases. -/
noncomputable def continuousTail405 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  majorTail328 ϕ G X N ϑ η - aliasCoefficient405 ϕ G X N ϑ η

/-- The actual smoothing family of Poisson aliases has a logarithm power one bound.
No off rational cancellation assumption enters this estimate. -/
theorem alias_family405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖aliasCoefficient405 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by
  classical
  obtain ⟨D, hD, hb⟩ := alias_multiplier405 hG ϑ hϑ
  obtain ⟨C, hC, hf⟩ := smoothed_family_bound261 hϕ
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro X hX η hη hscale
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hxp ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    dsimp [T]
    positivity
  let W : ℝ → ℂ := {α | MajorArc X R α}.indicator
    (fun α => continuousModel405 G R T α - bRhat G R T α)
  have hm : Measurable W :=
    ((measurable_continuousModel405 hG R T).sub
      (continuous_bRhat hG.supp hG.even R T hT).measurable).indicator
        (measurableSet_majorArc84 X R)
  have hWB (α : ℝ) : ‖W α‖ ≤ D * η ^ 2 := by
    by_cases ha : MajorArc X R α
    · simp only [W, Set.indicator, Set.mem_setOf_eq, if_pos ha]
      rw [norm_sub_rev]
      exact hb X hX η hη hscale α
    · simp only [W, Set.indicator, Set.mem_setOf_eq, if_neg ha, norm_zero]
      positivity
  have heq (N : ℕ) : aliasCoefficient405 ϕ G X N ϑ η =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases ha : MajorArc X R α <;> simp [aliasCoefficient405, W, R, T, Set.indicator, ha]
  simp_rw [heq]
  have hh := hf X hX W hm (D * η ^ 2) (by positivity) hWB
  convert hh using 1 <;> ring

/-- The smaller remainder is the coefficient of the central discrete term minus the
continuous rational model. The full rational sum aliases have been removed exactly.
The selected central transform remains discrete. -/
theorem continuousTail_eq_integral405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
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
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hxp ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    dsimp [T]
    positivity
  have hb := arcSquare_memLp328 ϕ
    (continuous_bRhat hG.supp hG.even R T hT) MeasurableSet.univ N
  have hb' : MemLp (fun α => Sphi ϕ N α ^ 2 * bRhat G R T α)
      2 (volume.restrict (Set.Ioc 0 1)) := by simpa [arcSquare328] using hb
  have hn := nearSquare_memLp328 ϕ hG.supp hxp hRp hη N
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
  let F : ℝ → ℂ := s.indicator (fun α => Sphi ϕ N α ^ 2 *
    (nearTransform328 G X R η α - bRhat G R T α))
  let H : ℝ → ℂ := s.indicator (fun α => Sphi ϕ N α ^ 2 *
    (continuousModel405 G R T α - bRhat G R T α))
  have hFp : MemLp F 2 (volume.restrict (Set.Ioc 0 1)) := by
    have hh := (hn.sub hb').indicator hs.nullMeasurableSet
    convert hh using 1
    funext α
    by_cases hα : α ∈ s <;> simp [F, Set.indicator, hα, mul_sub]
  have hHp : MemLp H 2 (volume.restrict (Set.Ioc 0 1)) :=
    ha.indicator hs.nullMeasurableSet
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hFi : IntervalIntegrable (fun α => F α * ee (-(N * α))) volume 0 1 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hFp.integrable (by norm_num : (1 : ENNReal) ≤ 2))).mul_continuousOn he.continuousOn
  have hHi : IntervalIntegrable (fun α => H α * ee (-(N * α))) volume 0 1 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hHp.integrable (by norm_num : (1 : ENNReal) ≤ 2))).mul_continuousOn he.continuousOn
  have hfull : majorTail328 ϕ G X N ϑ η = ∫ α in (0 : ℝ)..1, F α * ee (-(N * α)) := by
    rw [majorTail_eq_integral328 ϕ hG hX N ϑ hη]
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hh : α ∈ s <;> simp [F, R, T, s, Set.indicator] at hh ⊢ <;> simp_all
  have halias : aliasCoefficient405 ϕ G X N ϑ η = ∫ α in (0 : ℝ)..1, H α * ee (-(N * α)) := by
    unfold aliasCoefficient405
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hh : α ∈ s <;> simp [H, R, T, s, Set.indicator] at hh ⊢ <;> simp_all
  rw [continuousTail405, hfull, halias, ← intervalIntegral.integral_sub hFi hHi]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases hh : α ∈ s
  · have hh' : MajorArc X ((X : ℝ) ^ ϑ) α := hh
    simp [F, H, s, R, T, Set.indicator, hh']
    ring
  · have hh' : ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hh
    simp [F, H, s, R, T, Set.indicator, hh']

/-- LEAF. P0029 page 26 display 7.5 and page 27 major part of display 7.8.
OPEN central minus continuous family estimate. The full rational sum aliases are removed.
The selected central transform remains discrete.
The exact remaining integrand is given by continuousTail_eq_integral405.
This is strictly smaller than major_tail_family328 because alias_family405 is proved. -/
theorem continuous_tail_family405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖continuousTail405 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- Exact major_tail_family328 statement assembled from the continuous leaf and the
proved alias family. CONDITIONAL ON continuous_tail_family405. -/
theorem major_tail_supply405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorTail328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, hc⟩ := continuous_tail_family405 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, ha⟩ := alias_family405 hϕ hG ϑ hϑ
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
    (fun N => majorTail328 ϕ G X N ϑ η) (fun N => aliasCoefficient405 ϕ G X N ϑ η)
  change _ ≤ 2 * ((_ : ℝ) + ∑ N ∈ Finset.Icc 1 X,
    ‖continuousTail405 ϕ G X N ϑ η‖ ^ 2) at hsplit
  nlinarith [mul_le_mul_of_nonneg_left hlog5
    (by positivity : 0 ≤ C₂ * η ^ 4 * (X : ℝ) ^ 3)]

/-- The rational pair count can be absorbed at any prescribed power of X.
This is an algebraic scale identity, derived from page 26. -/
theorem alias_power_identity405 {x : ℝ} (hx : 0 < x) {ϑ : ℝ} (hϑ : 0 < ϑ) (δ : ℝ) :
    (x ^ ϑ) ^ 2 * (x ^ ϑ) ^ (-(2 + δ / ϑ)) = x ^ (-δ) := by
  have hRp : 0 < x ^ ϑ := Real.rpow_pos_of_pos hx ϑ
  rw [← Real.rpow_two, ← Real.rpow_add hRp, ← Real.rpow_mul hx.le]
  congr 1
  field_simp
  <;> ring

/-- The full rational sum of nonzero Poisson translates has arbitrary power decay in X.
The constant depends on the fixed positive theta and the requested nonnegative power. -/
theorem poisson_alias_decay405 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ α : ℝ,
      ‖bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
        continuousModel405 G ((X : ℝ) ^ ϑ)
          (fun q => η * X * q / (X : ℝ) ^ ϑ) α‖ ≤ D * (X : ℝ) ^ (-δ) := by
  have hA : 0 ≤ 2 + δ / ϑ := by positivity
  obtain ⟨D, hD, hb⟩ := continuousModel_error405 hG hA
  refine ⟨D, hD, fun X hX η hη hscale α => ?_⟩
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hx1 hϑ.le
  have hRp : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hxp ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊,
      (X : ℝ) ^ ϑ ≤ η * X * q / (X : ℝ) ^ ϑ := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    apply (le_div_iff₀ hRp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq1 (by positivity : 0 ≤ η * X),
      sq_nonneg ((X : ℝ) ^ ϑ)]
  have hh := hb _ _ hRp.le hR1 _ hT α
  rwa [mul_assoc, alias_power_identity405 hxp hϑ δ] at hh

/-- The Poisson alias coefficient on any measurable frequency set. -/
noncomputable def aliasOn405 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) (s : Set ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, s.indicator
    (fun α => Sphi ϕ N α ^ 2 *
      (continuousModel405 G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
        bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
      ee (-(N * α))) α

/-- Any measurable restriction of the alias coefficients has an arbitrarily small
power bound for its actual changing smoothing family. -/
theorem alias_on_family405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ s : Set ℝ, MeasurableSet s →
      ∑ N ∈ Finset.Icc 1 X, ‖aliasOn405 ϕ G X N ϑ η s‖ ^ 2 ≤
        C * ((X : ℝ) ^ (-δ)) ^ 2 * (X : ℝ) ^ 3 * Real.log X := by
  classical
  obtain ⟨D, hD, hb⟩ := poisson_alias_decay405 hG ϑ hϑ δ hδ
  obtain ⟨C, hC, hf⟩ := smoothed_family_bound261 hϕ
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro X hX η hη hscale s hs
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hxp ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    dsimp [T]
    positivity
  let W : ℝ → ℂ := s.indicator
    (fun α => continuousModel405 G R T α - bRhat G R T α)
  have hm : Measurable W :=
    ((measurable_continuousModel405 hG R T).sub
      (continuous_bRhat hG.supp hG.even R T hT).measurable).indicator hs
  have hWB (α : ℝ) : ‖W α‖ ≤ D * (X : ℝ) ^ (-δ) := by
    by_cases ha : α ∈ s
    · simp only [W, Set.indicator_of_mem ha, norm_sub_rev]
      exact hb X hX η hη hscale α
    · simp only [W, Set.indicator_of_notMem ha, norm_zero]
      positivity
  have heq (N : ℕ) : aliasOn405 ϕ G X N ϑ η s =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases ha : α ∈ s <;> simp [aliasOn405, W, R, T, Set.indicator, ha]
  simp_rw [heq]
  have hh := hf X hX W hm (D * (X : ℝ) ^ (-δ)) (by positivity) hWB
  convert hh using 1 <;> ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.centeredFourier_error405
#print axioms LeanLab.BhowmikGrimmelt2026.measurable_centeredFourier405
#print axioms LeanLab.BhowmikGrimmelt2026.measurable_continuousModel405
#print axioms LeanLab.BhowmikGrimmelt2026.continuousModel_error405
#print axioms LeanLab.BhowmikGrimmelt2026.alias_scale405

#print axioms LeanLab.BhowmikGrimmelt2026.alias_multiplier405
#print axioms LeanLab.BhowmikGrimmelt2026.alias_family405
#print axioms LeanLab.BhowmikGrimmelt2026.continuousTail_eq_integral405
#print axioms LeanLab.BhowmikGrimmelt2026.continuous_tail_family405
#print axioms LeanLab.BhowmikGrimmelt2026.major_tail_supply405

#print axioms LeanLab.BhowmikGrimmelt2026.alias_power_identity405
#print axioms LeanLab.BhowmikGrimmelt2026.poisson_alias_decay405
#print axioms LeanLab.BhowmikGrimmelt2026.alias_on_family405

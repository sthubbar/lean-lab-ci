/-
Supply for P0029 page 26 displays 7.4 to 7.7 and page 27 display 7.8.
Remove the selected central Poisson aliases as well as the full sum aliases.
Only the continuous off rational coefficient remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp405a
import LeanLab.BhowmikGrimmelt2026.TailRange432

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The selected central zero Poisson translates on the unit frequency interval.
Derived from page 26 displays 7.4 and 7.7 with the existing signed representatives. -/
noncomputable def nearContinuous432 (G : ℝ → ℝ) (X : ℕ) (R η α : ℝ) : ℂ := by
  classical
  exact ∑ q ∈ Finset.Icc 1 ⌊R⌋₊,
    ∑ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
      if |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X) then
        centeredFourier405 G (η * X * q / R) (α - (a : ℝ) / q) else 0

/-- On a central arc the selected continuous sum has exactly one rational term. -/
theorem nearContinuous_eq432 {G : ℝ → ℝ} {X : ℕ} {R η α : ℝ}
    (hX : 0 < (X : ℝ)) (hR : 0 ≤ R) (hsep : 2 * R ^ 2 < X)
    {q : ℕ} {a : ℤ} (hqmem : q ∈ Finset.Icc 1 ⌊R⌋₊)
    (hamem : a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1))
    (hclose : |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X)) :
    nearContinuous432 G X R η α =
      centeredFourier405 G (η * X * q / R) (α - (a : ℝ) / q) := by
  classical
  have hq := Finset.mem_Icc.mp hqmem
  have ha := Finset.mem_filter.mp hamem
  have hqR : (q : ℝ) ≤ R := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le hR)
  unfold nearContinuous432
  rw [Finset.sum_eq_single q]
  · rw [Finset.sum_eq_single a]
    · simp only [if_pos hclose]
    · intro b hb hba
      have hbn := Finset.mem_filter.mp hb
      have hnot : ¬ |α - (b : ℝ) / q| ≤ R / ((q : ℝ) * X) := by
        intro hbclose
        have hu := near_rational_unique328 hX hR hsep
          (by omega : 0 < q) (by omega : 0 < q) hqR hqR ha.2 hbn.2 hclose hbclose
        exact hba hu.2.symm
      exact if_neg hnot
    · intro hn
      exact False.elim (hn hamem)
  · intro r hr hrq
    apply Finset.sum_eq_zero
    intro b hb
    have hrn := Finset.mem_Icc.mp hr
    have hbn := Finset.mem_filter.mp hb
    have hrR : (r : ℝ) ≤ R := (Nat.cast_le.mpr hrn.2).trans (Nat.floor_le hR)
    have hnot : ¬ |α - (b : ℝ) / r| ≤ R / ((r : ℝ) * X) := by
      intro hbclose
      have hu := near_rational_unique328 hX hR hsep
        (by omega : 0 < q) (by omega : 0 < r) hqR hrR ha.2 hbn.2 hclose hbclose
      exact hrq hu.1.symm
    exact if_neg hnot
  · intro hn
    exact False.elim (hn hqmem)


/-- The finite selected continuous multiplier is measurable. -/
theorem measurable_nearContinuous432 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (X : ℕ) (R η : ℝ) : Measurable (nearContinuous432 G X R η) := by
  classical
  unfold nearContinuous432
  apply Finset.measurable_sum
  intro q hq
  apply Finset.measurable_sum
  intro a ha
  exact ((measurable_centeredFourier405 hG _).comp
    (measurable_id.sub_const _)).ite
    (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet
    measurable_const

/-- The selected central alias multiplier has the required eta squared bound.
Only one term is estimated, so no rational pair count is incurred. -/
theorem central_alias_multiplier432 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      MajorArc X ((X : ℝ) ^ ϑ) α →
      ‖nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
        nearContinuous432 G X ((X : ℝ) ^ ϑ) η α‖ ≤ D * η ^ 2 := by
  obtain ⟨D, hD, hb⟩ := centeredFourier_error405 hG (2 / ϑ)
  refine ⟨D, hD, ?_⟩
  intro X hX η hη hη1 hscale α hα hm
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXp ϑ
  have hηX : η * X ≤ (X : ℝ) := by nlinarith
  have hRX : (X : ℝ) ^ ϑ ≤ X := by nlinarith [sq_nonneg ((X : ℝ) ^ ϑ - 1)]
  have hsep : 2 * ((X : ℝ) ^ ϑ) ^ 2 < X := by nlinarith
  obtain ⟨q, hq, a, ha, hclose⟩ := majorArc_center_in_sum328 hXp hRX hα hm
  rw [nearTransform_eq328 hXp hRp.le hsep hq ha hclose,
    nearContinuous_eq432 hXp hRp.le hsep hq ha hclose]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hT : 1 ≤ η * X * q / (X : ℝ) ^ ϑ := by
    apply (le_div_iff₀ hRp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq1 (by positivity : 0 ≤ η * X),
      sq_nonneg ((X : ℝ) ^ ϑ - 1)]
  exact (hb _ _ hT).trans (mul_le_mul_of_nonneg_left
    (central_scale_tail328 hX1 hϑ hη hq1 hscale) hD.le)

/-- The selected central alias multiplier, restricted to major arcs of the unit interval. -/
noncomputable def centralAliasMultiplier432 (G : ℝ → ℝ) (X : ℕ) (ϑ η : ℝ) : ℝ → ℂ :=
  (Set.Icc (0 : ℝ) 1 ∩ {α | MajorArc X ((X : ℝ) ^ ϑ) α}).indicator
    (fun α => nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
      nearContinuous432 G X ((X : ℝ) ^ ϑ) η α)

/-- The selected alias multiplier is measurable at positive scales. -/
theorem measurable_centralAliasMultiplier432 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) {η : ℝ} (hη : 0 < η) :
    Measurable (centralAliasMultiplier432 G X ϑ η) := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  exact ((measurable_nearTransform328 hG.supp hXp
    (Real.rpow_pos_of_pos hXp ϑ) hη).sub
      (measurable_nearContinuous432 hG X _ η)).indicator
    (measurableSet_Icc.inter (measurableSet_majorArc84 X _))

/-- The selected central alias coefficient uses the actual smoothing scale N. -/
noncomputable def centralAlias432 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * centralAliasMultiplier432 G X ϑ η α *
    ee (-(N * α))

/-- The selected aliases have a family bound with logarithm power one. -/
theorem central_alias_family432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖centralAlias432 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by
  classical
  obtain ⟨D, hD, hb⟩ := central_alias_multiplier432 hG ϑ hϑ
  obtain ⟨C, hC, hf⟩ := smoothed_family_bound261 hϕ
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hm := measurable_centralAliasMultiplier432 hG hX ϑ hη
  have hWB (α : ℝ) : ‖centralAliasMultiplier432 G X ϑ η α‖ ≤ D * η ^ 2 := by
    by_cases ha : α ∈ Set.Icc (0 : ℝ) 1 ∩ {α | MajorArc X ((X : ℝ) ^ ϑ) α}
    · rw [centralAliasMultiplier432, Set.indicator_of_mem ha]
      exact hb X hX η hη hη1 hscale α ha.1 ha.2
    · rw [centralAliasMultiplier432, Set.indicator_of_notMem ha, norm_zero]
      positivity
  have hh := hf X hX _ hm (D * η ^ 2) (by positivity) hWB
  change (∑ N ∈ Finset.Icc 1 X,
    ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * centralAliasMultiplier432 G X ϑ η α *
      ee (-(N * α))‖ ^ 2) ≤ _
  convert hh using 1 <;> ring

/-- The purely continuous off rational coefficient after both alias contributions are removed. -/
noncomputable def offRational432 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  continuousTail405 ϕ G X N ϑ η - centralAlias432 ϕ G X N ϑ η

/-- The continuous remainder integrand has a genuine interval integral. -/
theorem continuousTail_integrable432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    IntervalIntegrable
      (fun α => {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
        (fun α => Sphi ϕ N α ^ 2 *
          (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
            continuousModel405 G ((X : ℝ) ^ ϑ)
              (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α) volume 0 1 := by
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
  have hdiff : IntervalIntegrable
      (fun α => (F α - H α) * ee (-(N * α))) volume 0 1 := by
    convert hFi.sub hHi using 1
    funext α
    ring
  convert hdiff using 1
  funext α
  by_cases hh : α ∈ s
  · have hh' : MajorArc X ((X : ℝ) ^ ϑ) α := hh
    simp only [F, H, s, R, T, Set.indicator, Set.mem_setOf_eq, if_pos hh']
    ring
  · have hh' : ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hh
    simp [F, H, s, R, T, Set.indicator, hh']

/-- The selected alias coefficient has an interval integrable integrand. -/
theorem centralAlias_integrable432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    IntervalIntegrable (fun α => Sphi ϕ N α ^ 2 *
      centralAliasMultiplier432 G X ϑ η α * ee (-(N * α))) volume 0 1 := by
  classical
  obtain ⟨D, hD, hb⟩ := central_alias_multiplier432 hG ϑ hϑ
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hMb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left _ _)
  have hWB (α : ℝ) : ‖centralAliasMultiplier432 G X ϑ η α‖ ≤ D * η ^ 2 := by
    by_cases ha : α ∈ Set.Icc (0 : ℝ) 1 ∩ {α | MajorArc X ((X : ℝ) ^ ϑ) α}
    · rw [centralAliasMultiplier432, Set.indicator_of_mem ha]
      exact hb X hX η hη hη1 hscale α ha.1 ha.2
    · rw [centralAliasMultiplier432, Set.indicator_of_notMem ha, norm_zero]
      positivity
  have hLp := smoothed_multiplier_memLp261 (le_max_right M 0) hMb
    (measurable_centralAliasMultiplier432 hG hX ϑ hη)
    (by positivity : 0 ≤ D * η ^ 2) hWB N
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (hLp.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  exact hi.mul_continuousOn
    (ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)).continuousOn

/-- The last remainder contains only continuous zero Poisson translates.
This identifies the smaller leaf integrand without invoking any OPEN estimate. -/
theorem offRational_eq_integral432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {X : ℕ} (hX : 2 ≤ X) (N : ℕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) :
    offRational432 ϕ G X N ϑ η =
      ∫ α in (0 : ℝ)..1, {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
        (fun α => Sphi ϕ N α ^ 2 *
          (nearContinuous432 G X ((X : ℝ) ^ ϑ) η α -
            continuousModel405 G ((X : ℝ) ^ ϑ)
              (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α := by
  classical
  rw [offRational432, continuousTail_eq_integral405 hϕ hG hX N ϑ hϑ hη hscale,
    centralAlias432, ← intervalIntegral.integral_sub
      (continuousTail_integrable432 hϕ hG hX N ϑ hϑ hη hscale)
      (centralAlias_integrable432 hϕ hG hX N ϑ hϑ hη hη1 hscale)]
  apply intervalIntegral.integral_congr
  intro α hα
  have hα' : α ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα
  by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
  · have ha : α ∈ Set.Icc (0 : ℝ) 1 ∩ {α | MajorArc X ((X : ℝ) ^ ϑ) α} := ⟨hα', hm⟩
    simp [centralAliasMultiplier432, Set.indicator_of_mem ha, Set.indicator, hm, hα']
    ring
  · simp [centralAliasMultiplier432, Set.indicator, hm]

/-- LEAF. P0029 page 26 displays 7.4 to 7.7 and page 27 major part of 7.8.
OPEN continuous off rational family for R at least two and eta below X to theta minus one half.
Both the full rational sum aliases and the selected central aliases have clean family bounds.
The exact purely continuous integrand is offRational_eq_integral432.
This excludes the proved single denominator case and is strictly smaller than the original tail. -/
theorem off_rational_family432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖offRational432 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- The exact original tail statement assembled from the smaller continuous leaf.
CONDITIONAL ON off_rational_family432. No direct sorry occurs in this assembly. -/
theorem major_tail_supply432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorTail328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₀, hC₀, h₀⟩ := off_rational_family432 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₁, hC₁, h₁⟩ := central_alias_family432 hϕ hG ϑ hϑ
  obtain ⟨C₂, hC₂, h₂⟩ := alias_family405 hϕ hG ϑ hϑ
  obtain ⟨C₃, hC₃, h₃⟩ := major_tail_large_eta432 hϕ hG ϑ hϑ hϑ'
  let C : ℝ := 4 * C₀ + 64 * C₁ + 32 * C₂ + 16 * C₃
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ X by exact_mod_cast hX)
    linarith [Real.log_two_gt_d9]
  have hlog : 0 ≤ Real.log (X : ℝ) := by linarith
  have hlog5 : Real.log (X : ℝ) ≤ 16 * Real.log X ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
    have hh := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ Real.log (X : ℝ))
    norm_num at hh
    nlinarith only [hh]
  by_cases hlarge : (X : ℝ) ^ (ϑ - 1 / 2) ≤ η
  · have hh := h₃ X hX η hη hη1 hlarge hscale
    have hC : 16 * C₃ ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ C₃ * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := hh
      _ ≤ (16 * C₃) * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
        nlinarith [mul_le_mul_of_nonneg_left hlog5
          (by positivity : 0 ≤ C₃ * η ^ 4 * (X : ℝ) ^ 3)]
      _ ≤ C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
        gcongr <;> assumption
  by_cases hR : 2 ≤ (X : ℝ) ^ ϑ
  · have hpure := h₀ X hX hR η hη hη1 (lt_of_not_ge hlarge) hscale
    have hcentral := h₁ X hX η hη hη1 hscale
    have halias := h₂ X hX η hη hscale
    have hsplit₁ := coefficient_split328 (Finset.Icc 1 X)
      (fun N => majorTail328 ϕ G X N ϑ η) (fun N => aliasCoefficient405 ϕ G X N ϑ η)
    have hsplit₂ := coefficient_split328 (Finset.Icc 1 X)
      (fun N => continuousTail405 ϕ G X N ϑ η) (fun N => centralAlias432 ϕ G X N ϑ η)
    change _ ≤ 2 * ((_ : ℝ) + ∑ N ∈ Finset.Icc 1 X,
      ‖continuousTail405 ϕ G X N ϑ η‖ ^ 2) at hsplit₁
    change _ ≤ 2 * ((_ : ℝ) + ∑ N ∈ Finset.Icc 1 X,
      ‖offRational432 ϕ G X N ϑ η‖ ^ 2) at hsplit₂
    dsimp [C]
    nlinarith [mul_nonneg hC₃ (by positivity : 0 ≤ η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5),
      mul_le_mul_of_nonneg_left hlog5
      (by positivity : 0 ≤ C₁ * η ^ 4 * (X : ℝ) ^ 3),
      mul_le_mul_of_nonneg_left hlog5
      (by positivity : 0 ≤ C₂ * η ^ 4 * (X : ℝ) ^ 3)]
  · have hz (N : ℕ) := majorTail_single_denominator328 ϕ hG hX N hϑ hη hη1 hscale
      (lt_of_not_ge hR)
    simp_rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
    dsimp [C]
    positivity

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.nearContinuous432
#print axioms LeanLab.BhowmikGrimmelt2026.nearContinuous_eq432
#print axioms LeanLab.BhowmikGrimmelt2026.measurable_nearContinuous432
#print axioms LeanLab.BhowmikGrimmelt2026.central_alias_multiplier432

#print axioms LeanLab.BhowmikGrimmelt2026.central_alias_family432

#print axioms LeanLab.BhowmikGrimmelt2026.continuousTail_integrable432
#print axioms LeanLab.BhowmikGrimmelt2026.centralAlias_integrable432
#print axioms LeanLab.BhowmikGrimmelt2026.offRational_eq_integral432
#print axioms LeanLab.BhowmikGrimmelt2026.off_rational_family432
#print axioms LeanLab.BhowmikGrimmelt2026.major_tail_supply432

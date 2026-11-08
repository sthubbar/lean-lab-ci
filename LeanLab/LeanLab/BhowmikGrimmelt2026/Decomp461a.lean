/-
A denominator split of the continuous off rational coefficient in P0029 pages 26 and 27.
Central denominators through square root R have a proved eta squared multiplier bound.
The larger denominator family is the only new OPEN leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.DenominatorPower461

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The continuous off rational multiplier on central arcs with denominator at most square root R.
The unit interval restriction keeps the selected signed representative convention. -/
noncomputable def smallDenMultiplier461 (G : ℝ → ℝ) (X : ℕ) (R η α : ℝ) : ℂ := by
  classical
  exact {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ q ∈ Finset.Icc 1 ⌊R⌋₊,
      ∃ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
        (q : ℝ) ≤ Real.sqrt R ∧ |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X)}.indicator
    (fun α => nearContinuous432 G X R η α -
      continuousModel405 G R (fun q => η * X * q / R) α) α

/-- The unit interval central arcs through square root R form a measurable set. -/
theorem measurableSet_smallDen461 (X : ℕ) (R : ℝ) :
    MeasurableSet {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ q ∈ Finset.Icc 1 ⌊R⌋₊,
        ∃ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
          (q : ℝ) ≤ Real.sqrt R ∧ |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X)} := by
  classical
  simp only [Set.setOf_and, Set.setOf_exists]
  apply measurableSet_Icc.inter
  apply MeasurableSet.iUnion
  intro q
  by_cases hq : q ∈ Finset.Icc 1 ⌊R⌋₊
  · simp only [hq, Set.setOf_true, Set.univ_inter]
    apply MeasurableSet.iUnion
    intro a
    by_cases ha : a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter
        (fun a => Int.gcd a q = 1)
    · simp only [ha, Set.setOf_true, Set.univ_inter]
      by_cases hd : (q : ℝ) ≤ Real.sqrt R
      · simpa only [hd, Set.setOf_true, Set.univ_inter, Pi.sub_apply, id_eq] using
          (isClosed_le (continuous_id.sub (continuous_const (y := (a : ℝ) / q))).abs
            (continuous_const (y := R / ((q : ℝ) * X)))).measurableSet
      · simp [hd]
    · simp [ha]
  · simp [hq]

/-- The small denominator multiplier is measurable. -/
theorem measurable_smallDenMultiplier461 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (X : ℕ) (R η : ℝ) : Measurable (smallDenMultiplier461 G X R η) := by
  unfold smallDenMultiplier461
  exact ((measurable_nearContinuous432 hG X R η).sub
    (measurable_continuousModel405 hG R (fun q => η * X * q / R))).indicator
    (measurableSet_smallDen461 X R)

/-- Small central denominators have a uniform eta squared continuous off rational error.
The estimate sums all other reduced pairs rather than replacing them by one maximum. -/
theorem small_denominator_multiplier461 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ α : ℝ,
      ‖smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α‖ ≤ D * η ^ 2 := by
  classical
  obtain ⟨D, hD, hb⟩ := sqrt_denominator_off_sum461 hG ϑ hϑ
  refine ⟨D, hD, ?_⟩
  intro X hX η hη hη1 hscale α
  let R : ℝ := (X : ℝ) ^ ϑ
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hXp ϑ
  have hηX : η * X ≤ (X : ℝ) := by nlinarith
  have hRX : 10 * R ^ 2 ≤ (X : ℝ) := hscale.trans hηX
  have hsep : 2 * R ^ 2 < (X : ℝ) := by nlinarith [sq_pos_of_pos hRp]
  change ‖smallDenMultiplier461 G X R η α‖ ≤ D * η ^ 2
  unfold smallDenMultiplier461
  simp only [Set.indicator, Set.mem_setOf_eq]
  split_ifs with hs
  · obtain ⟨hα, q, hq, a, ha, hden, hclose⟩ := hs
    have hqn := Finset.mem_Icc.mp hq
    have han := (Finset.mem_filter.mp ha).2
    obtain ⟨b, hbq, hcop, k, heq⟩ := reduced_residue_of_int (by omega : 0 < q) han
    let p₀ : Σ _ : ℕ, ℕ := ⟨q, b⟩
    have hp₀ : p₀ ∈ reducedPairs ⌊R⌋₊ :=
      (mem_reducedPairs _ _).mpr ⟨hqn.1, hqn.2, hbq, hcop⟩
    have hd : α - (a : ℝ) / q = (α - (b : ℝ) / q) + ((-k : ℤ) : ℝ) := by
      rw [heq, Int.cast_neg]
      ring
    have hn : nearContinuous432 G X R η α =
        centeredFourier405 G (η * X * p₀.1 / R) (α - p₀.2 / p₀.1) := by
      rw [nearContinuous_eq432 hXp hRp.le hsep hq ha hclose, hd,
        centeredFourier_add_int432]
    have hc : (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) ≤ R / X := by
      have hl : intDist (α - (b : ℝ) / q) ≤ |α - (a : ℝ) / q| := by
        convert intDist_le_abs_sub (α - (b : ℝ) / q) k using 1
        congr 1
        linarith only [heq]
      have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hh := mul_le_mul_of_nonneg_left (hl.trans hclose) hqp.le
      change (q : ℝ) * intDist (α - (b : ℝ) / q) ≤ _
      calc
        _ ≤ (q : ℝ) * (R / ((q : ℝ) * X)) := hh
        _ = _ := by field_simp
    rw [hn, continuousModel405, ← sum_reducedPairs,
      ← Finset.sum_erase_add _ _ hp₀,
      show centeredFourier405 G (η * X * p₀.1 / R) (α - p₀.2 / p₀.1) -
        ((∑ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
          centeredFourier405 G (η * X * p.1 / R) (α - p.2 / p.1)) +
          centeredFourier405 G (η * X * p₀.1 / R) (α - p₀.2 / p₀.1)) =
        -(∑ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
          centeredFourier405 G (η * X * p.1 / R) (α - p.2 / p.1)) by ring,
      norm_neg]
    exact hb X hX η hη hη1 hscale α p₀ hp₀ hden hc
  · simp only [norm_zero]
    positivity

/-- The actual changing smoothing coefficient on the small denominator central arcs. -/
noncomputable def smallDenCoefficient461 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
    smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η α * ee (-(N * α))

/-- The small denominator part has logarithm power one for the actual smoothing family. -/
theorem small_denominator_family461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖smallDenCoefficient461 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by
  obtain ⟨D, hD, hb⟩ := small_denominator_multiplier461 hG ϑ hϑ
  obtain ⟨C, hC, hf⟩ := smoothed_family_bound261 hϕ
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hbound := hb X hX η hη hη1 hscale
  have hh := hf X hX (smallDenMultiplier461 G X ((X : ℝ) ^ ϑ) η)
    (measurable_smallDenMultiplier461 hG X _ η) (D * η ^ 2) (by positivity) hbound
  change (∑ N ∈ Finset.Icc 1 X, ‖smallDenCoefficient461 ϕ G X N ϑ η‖ ^ 2) ≤ _ at hh
  convert hh using 1 <;> ring

/-- LEAF. P0029 page 26 displays 7.5 and 7.6 and page 27 major part of 7.8.
OPEN continuous off rational family after removing the small central denominator arcs.
The removed coefficient has a clean logarithm power one bound.
The remainder retains only central denominators greater than square root R.
It also excludes the previously proved large eta and single denominator ranges. -/
theorem large_denominator_family461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖offRational432 ϕ G X N ϑ η - smallDenCoefficient461 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- The exact continuous small eta family assembled from the larger denominator leaf.
CONDITIONAL ON large_denominator_family461. -/
theorem off_rational_supply461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → η < (X : ℝ) ^ (ϑ - 1 / 2) →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖offRational432 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₀, hC₀, h₀⟩ := small_denominator_family461 hϕ hG ϑ hϑ
  obtain ⟨C₁, hC₁, h₁⟩ := large_denominator_family461 hϕ hG ϑ hϑ hϑ'
  refine ⟨32 * C₀ + 2 * C₁, by positivity, ?_⟩
  intro X hX hR η hη hη1 hsmall hscale
  have hlog := Real.log_natCast_nonneg X
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ X by exact_mod_cast hX)
    linarith [Real.log_two_gt_d9]
  have hlog5 : Real.log (X : ℝ) ≤ 16 * Real.log X ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
    have hh := mul_le_mul_of_nonneg_right hp hlog
    norm_num at hh
    nlinarith only [hh]
  have hlow := h₀ X hX η hη hη1 hscale
  have hhigh := h₁ X hX hR η hη hη1 hsmall hscale
  have hsplit := coefficient_split328 (Finset.Icc 1 X)
    (fun N => offRational432 ϕ G X N ϑ η)
    (fun N => smallDenCoefficient461 ϕ G X N ϑ η)
  have hup := mul_le_mul_of_nonneg_left hlog5
    (by positivity : 0 ≤ C₀ * η ^ 4 * (X : ℝ) ^ 3)
  nlinarith only [hlow, hhigh, hsplit, hup]

/-- The exact original tail statement assembled from the smaller continuous leaf.
CONDITIONAL ON large_denominator_family461. No direct sorry occurs in this assembly. -/
theorem major_tail_supply461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorTail328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₀, hC₀, h₀⟩ := off_rational_supply461 hϕ hG ϑ hϑ hϑ'
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

#print axioms LeanLab.BhowmikGrimmelt2026.smallDenMultiplier461
#print axioms LeanLab.BhowmikGrimmelt2026.measurable_smallDenMultiplier461
#print axioms LeanLab.BhowmikGrimmelt2026.small_denominator_multiplier461
#print axioms LeanLab.BhowmikGrimmelt2026.smallDenCoefficient461
#print axioms LeanLab.BhowmikGrimmelt2026.small_denominator_family461

#print axioms LeanLab.BhowmikGrimmelt2026.large_denominator_family461
#print axioms LeanLab.BhowmikGrimmelt2026.off_rational_supply461
#print axioms LeanLab.BhowmikGrimmelt2026.major_tail_supply461

#print axioms LeanLab.BhowmikGrimmelt2026.measurableSet_smallDen461

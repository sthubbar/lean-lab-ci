/-
The continuous tail family on the integer central arcs.
Source: P0029 page 26 displays 7.5 to 7.7 and page 27 display 7.8.
This is a derived subregion of the proved square root denominator range.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp461a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- Integer distance is measurable for the nearest integer convention used by the paper. -/
theorem measurable_intDist461 : Measurable intDist := by
  have hr : Measurable (fun α : ℝ => round α) := by
    simp_rw [round_eq]
    exact (measurable_id.add_const (1 / 2 : ℝ)).floor
  have hc : Measurable (fun α : ℝ => ((round α : ℤ) : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hr
  exact (measurable_id.sub hc).abs

/-- The continuous tail on the integer central arcs has the original fifth logarithm budget.
No family bound for the other rational centers enters this proof. -/
theorem integer_arc_tail_family461 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨D₀, hD₀, hb₀⟩ := small_denominator_multiplier461 hG ϑ hϑ
  obtain ⟨D₁, hD₁, hb₁⟩ := central_alias_multiplier432 hG ϑ hϑ
  obtain ⟨C, hC, hf⟩ := smoothed_family_bound261 hϕ
  refine ⟨16 * C * (D₀ + D₁) ^ 2, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  let R : ℝ := (X : ℝ) ^ ϑ
  let s : Set ℝ := Set.Icc 0 1 ∩
    ({α : ℝ | MajorArc X R α} ∩ {α : ℝ | intDist α ≤ R / X})
  let W : ℝ → ℂ := s.indicator (fun α => smallDenMultiplier461 G X R η α +
    (nearTransform328 G X R η α - nearContinuous432 G X R η α))
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hXp ϑ
  have hR1 : 1 ≤ R := Real.one_le_rpow
    (by exact_mod_cast (by omega : 1 ≤ X)) hϑ.le
  have hs : MeasurableSet s := measurableSet_Icc.inter
    ((measurableSet_majorArc84 X R).inter (measurableSet_le measurable_intDist461 measurable_const))
  have hW : Measurable W :=
    ((measurable_smallDenMultiplier461 hG X R η).add
      ((measurable_nearTransform328 hG.supp hXp hRp hη).sub
        (measurable_nearContinuous432 hG X R η))).indicator hs
  have hWB : ∀ α, ‖W α‖ ≤ (D₀ + D₁) * η ^ 2 := by
    intro α
    by_cases ha : α ∈ s
    · dsimp only [W]
      rw [Set.indicator_of_mem ha]
      have hh := hb₁ X hX η hη hη1 hscale α ha.1 ha.2.1
      exact (norm_add_le _ _).trans (by
        have hlow := hb₀ X hX η hη hη1 hscale α
        dsimp only [R]
        nlinarith only [hh, hlow])
    · dsimp only [W]
      rw [Set.indicator_of_notMem ha, norm_zero]
      positivity
  have hb := hf X hX W hW ((D₀ + D₁) * η ^ 2) (by positivity) hWB
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) =
      ∫ α in (0 : ℝ)..1,
        ({α : ℝ | MajorArc X R α} ∩ {α : ℝ | intDist α ≤ R / X}).indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (nearTransform328 G X R η α -
              continuousModel405 G R (fun q => η * X * q / R) α) * ee (-(N * α))) α := by
    apply intervalIntegral.integral_congr
    intro α hα
    have hα' : α ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα
    by_cases ha : α ∈ {α : ℝ | MajorArc X R α} ∩ {α : ℝ | intDist α ≤ R / X}
    · have hmem : α ∈ s := ⟨hα', ha⟩
      have hr := abs_le.mp (abs_sub_round α)
      have hra : (round α : ℤ) ∈
          (Finset.Icc (-(1 : ℤ)) (2 * (1 : ℤ))).filter (fun a => Int.gcd a 1 = 1) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, by simp⟩
        · have hh : (-1 : ℝ) ≤ (round α : ℤ) := by linarith [hα'.1]
          exact_mod_cast hh
        · have hh : ((round α : ℤ) : ℝ) ≤ 2 := by linarith [hα'.2]
          exact_mod_cast hh
      have hsmall : α ∈ {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧
          ∃ q ∈ Finset.Icc 1 ⌊R⌋₊,
            ∃ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
              (q : ℝ) ≤ Real.sqrt R ∧ |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X)} := by
        refine ⟨hα', 1, Finset.mem_Icc.mpr ⟨by omega, (show (1 : ℕ) ≤ ⌊R⌋₊ from Nat.le_floor (by simpa using hR1))⟩,
          round α, hra, ?_, ?_⟩
        · exact (Real.le_sqrt (by norm_num) hRp.le).mpr (by simpa using hR1)
        · simpa only [Nat.cast_one, div_one, one_mul, Set.mem_setOf_eq, intDist] using ha.2
      dsimp only [W]
      rw [Set.indicator_of_mem hmem, smallDenMultiplier461, Set.indicator_of_mem hsmall,
        Set.indicator_of_mem ha]
      ring
    · have hn : α ∉ s := fun hh => ha hh.2
      dsimp only [W]
      rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem ha]
      simp
  simp_rw [heq] at hb
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
  change (∑ N ∈ Finset.Icc 1 X, _) ≤ _
  have hup := mul_le_mul_of_nonneg_left hlog5
    (by positivity : 0 ≤ C * (D₀ + D₁) ^ 2 * η ^ 4 * (X : ℝ) ^ 3)
  dsimp only [R] at hb
  change (∑ N ∈ Finset.Icc 1 X, _) ≤ _ at hb
  simpa only [intDist] using (by nlinarith only [hb, hup] :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩ {α : ℝ | intDist α ≤ (X : ℝ) ^ ϑ / X}).indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
              continuousModel405 G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
            ee (-(N * α))) α‖ ^ 2) ≤
      (16 * C * (D₀ + D₁) ^ 2) * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.measurable_intDist461
#print axioms LeanLab.BhowmikGrimmelt2026.integer_arc_tail_family461

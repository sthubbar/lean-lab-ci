/-
Higher prime power removal under the weighted minor multiplier.
Source: P0029 page 4 and page 27 display 7.8.
The estimates below keep the full bRhat multiplier and its scale condition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.PrimeMinorReduction451
import LeanLab.BhowmikGrimmelt2026.Lemma72Proof

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The higher prime power family estimate scales quadratically with a multiplier bound. -/
theorem prime_power_family_bounded451 {ϕ : ℝ → ℝ} {M B : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (hB : 0 ≤ B) {X : ℕ} (hX : 2 ≤ X)
    (W : ℕ → ℝ → ℂ) (hW : ∀ N α, ‖W N α‖ ≤ B) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) * W N α‖ ^ 2) ≤
        48 * M ^ 4 * B ^ 2 * (X : ℝ) ^ 2 * Real.sqrt X * Real.log X ^ 3 := by
  by_cases hB0 : B = 0
  · have hz (N : ℕ) (α : ℝ) : W N α = 0 :=
      norm_eq_zero.mp (le_antisymm (by simpa only [hB0] using hW N α) (norm_nonneg _))
    simp [hz, hB0]
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB0
  let V : ℕ → ℝ → ℂ := fun N α => W N α / (B : ℂ)
  have hV (N : ℕ) (α : ℝ) : ‖V N α‖ ≤ 1 := by
    dsimp [V]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBp]
    exact (div_le_one hBp).mpr (hW N α)
  have hf := prime_power_family_defect451 hM hbound hX V hV
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) * W N α) =
        (B : ℂ) * (∫ α in (0 : ℝ)..1,
          (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) * V N α) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro α hα
    dsimp [V]
    field_simp [hBc]
  calc
    _ = B ^ 2 * ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) * V N α‖ ^ 2 := by
      simp_rw [heq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBp]
      rw [Finset.mul_sum]
    _ ≤ B ^ 2 * (48 * M ^ 4 * (X : ℝ) ^ 2 * Real.sqrt X * Real.log X ^ 3) :=
      mul_le_mul_of_nonneg_left hf (sq_nonneg B)
    _ = _ := by ring

/-- A polynomial bound for the full minor weight follows without discarding its remainder.
This bound is deliberately weaker than the uniform bound asserted in the paper. -/
theorem minor_weight_polynomial451 {G : ℝ → ℝ} (hG : IsMajorWeight G) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℕ, ∀ R η : ℝ, 1 ≤ R → 0 < η → η ≤ 1 →
      10 * R ^ 2 ≤ η * X → ∀ α : ℝ, ¬ MajorArc X R α →
        ‖bRhat G R (fun q => η * X * q / R) α‖ ≤ D * R ^ 2 := by
  obtain ⟨C, hc⟩ := lemma72 G hG 1 (by norm_num)
  refine ⟨2 * max C 1, by positivity, ?_⟩
  intro X R η hR hη hη1 hscale α hminor
  have hRp : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hK : 1 ≤ η * X / R ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hRp)).mpr
    nlinarith
  have hE : (η * X / R ^ 2) ^ (-(1 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hK (by norm_num)
  have hb := (hc X R η hR hη hη1 hscale α).2 hminor
  have h0 : 0 ≤ (η * X / R ^ 2) ^ (-(1 : ℝ)) := by positivity
  have h1 := mul_le_mul_of_nonneg_right (le_max_left C 1)
    (by positivity : 0 ≤ 1 + R ^ 2 * (η * X / R ^ 2) ^ (-(1 : ℝ)))
  have h2 := mul_le_mul_of_nonneg_left hE (sq_nonneg R)
  have h3 := mul_le_mul_of_nonneg_left h2 (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right C 1))
  have h4 := mul_le_mul_of_nonneg_left hR2 (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right C 1))
  nlinarith only [hb, h1, h3, h4]

/-- The polynomial minor weight loss still fits inverse R when theta is at most one tenth. -/
theorem weighted_defect_power451 {x ϑ : ℝ} (hx : 1 ≤ x) (hϑ : ϑ ≤ 1 / 10) :
    (x ^ ϑ) ^ 4 * x ^ 2 * Real.sqrt x ≤ (x ^ ϑ)⁻¹ * x ^ 3 := by
  have hxp : 0 < x := by linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hxp.le,
    ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_add hxp, ← Real.rpow_add hxp,
    ← Real.rpow_neg_one, ← Real.rpow_mul hxp.le, ← Real.rpow_add hxp]
  apply Real.rpow_le_rpow_of_exponent_le hx
  linarith

/-- The weighted minor coefficient using only prime terms of the smoothing sum. -/
noncomputable def minorPrimeWeighted451 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  -(∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
    (fun α => primeSphi451 ϕ N α ^ 2 *
      bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
      ee (-(N * α))) α)

/-- The weighted coefficient defect has the exact bounded multiplier form. -/
theorem minorWeighted_sub_prime451 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϕ : ℝ → ℝ) {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (ϑ : ℝ)
    {η : ℝ} (hη : 0 < η) :
    minorWeighted328 ϕ G X N ϑ η - minorPrimeWeighted451 ϕ G X N ϑ η =
      ∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) *
        {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => -bRhat G ((X : ℝ) ^ ϑ)
            (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))) α := by
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  let s : Set ℝ := {α | ¬ MajorArc X R α}
  have hs : MeasurableSet s := (measurableSet_majorArc84 X R).compl
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hxp ϑ
  have hT (q : ℕ) (hq : q ∈ Finset.Icc 1 ⌊R⌋₊) : 0 < T q := by
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    dsimp [T]
    positivity
  have hc := continuous_bRhat hG.supp hG.even R T hT
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  let F : ℝ → ℂ := s.indicator (fun α => Sphi ϕ N α ^ 2 * bRhat G R T α * ee (-(N * α)))
  let H : ℝ → ℂ := s.indicator (fun α => primeSphi451 ϕ N α ^ 2 * bRhat G R T α * ee (-(N * α)))
  have hFc : Continuous (fun α => Sphi ϕ N α ^ 2 * bRhat G R T α * ee (-(N * α))) :=
    (((continuous_Sphi ϕ N).pow 2).mul hc).mul he
  have hHc : Continuous (fun α => primeSphi451 ϕ N α ^ 2 * bRhat G R T α * ee (-(N * α))) :=
    ((((continuous_prime_parts451 ϕ N).1).pow 2).mul hc).mul he
  have hFi : IntervalIntegrable F volume 0 1 :=
    ⟨(hFc.intervalIntegrable 0 1).1.indicator hs, (hFc.intervalIntegrable 0 1).2.indicator hs⟩
  have hHi : IntervalIntegrable H volume 0 1 :=
    ⟨(hHc.intervalIntegrable 0 1).1.indicator hs, (hHc.intervalIntegrable 0 1).2.indicator hs⟩
  rw [minorWeighted_eq_integral328 hG ϕ hX N ϑ hη]
  change -(∫ α in (0 : ℝ)..1, F α) - (-(∫ α in (0 : ℝ)..1, H α)) = _
  rw [show -(∫ α in (0 : ℝ)..1, F α) - (-(∫ α in (0 : ℝ)..1, H α)) =
      -((∫ α in (0 : ℝ)..1, F α) - (∫ α in (0 : ℝ)..1, H α)) by ring,
    ← intervalIntegral.integral_sub hFi hHi, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases hm : α ∈ s
  · have hm' : ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hm
    simp [F, H, s, R, T, Set.indicator, hm']
    ring
  · have hm' : ¬ ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hm
    simp [F, H, s, R, T, Set.indicator, hm']

/-- Higher prime powers fit the exact weighted minor budget for theta up to one tenth.
The full multiplier remains present and no uniform constant multiplier estimate is assumed. -/
theorem weighted_prime_defect_family451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 ≤ ϑ) (hϑ' : ϑ ≤ 1 / 10) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖minorWeighted328 ϕ G X N ϑ η - minorPrimeWeighted451 ϕ G X N ϑ η‖ ^ 2 ≤
          C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
            (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hbound : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left _ _)
  obtain ⟨D, hD, hd⟩ := minor_weight_polynomial451 hG
  refine ⟨192 * (max M 0) ^ 4 * D ^ 2, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  let R : ℝ := (X : ℝ) ^ ϑ
  have hR : 1 ≤ R := Real.one_le_rpow hx1 hϑ
  let W : ℕ → ℝ → ℂ := fun N α =>
    {α | ¬ MajorArc X R α}.indicator
      (fun α => -bRhat G R (fun q => η * X * q / R) α * ee (-(N * α))) α
  have hW (N : ℕ) (α : ℝ) : ‖W N α‖ ≤ D * R ^ 2 := by
    by_cases hm : MajorArc X R α
    · simp [W, Set.indicator, hm]
      positivity
    · simpa [W, Set.indicator, hm, norm_mul, ee_eq_library84,
        LeanLab.PNTPort.LargeSieve.norm_e] using hd X R η hR hη hη1 hscale α hm
  have hb := prime_power_family_bounded451 (le_max_right M 0) hbound
    (by positivity : 0 ≤ D * R ^ 2) hX W hW
  simp_rw [minorWeighted_sub_prime451 hG ϕ hX _ ϑ hη]
  apply hb.trans
  have hp := weighted_defect_power451 hx1 hϑ'
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ X by exact_mod_cast hX)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by linarith [Real.log_two_gt_d9]
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 2
  have hm := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ Real.log (X : ℝ) ^ 3)
  have hl : Real.log (X : ℝ) ^ 3 ≤ 4 * Real.log X ^ 5 := by
    norm_num at hm
    nlinarith only [hm]
  calc
    _ = (48 * (max M 0) ^ 4 * D ^ 2) *
        (R ^ 4 * (X : ℝ) ^ 2 * Real.sqrt X) * Real.log X ^ 3 := by ring
    _ ≤ (48 * (max M 0) ^ 4 * D ^ 2) *
        (R⁻¹ * (X : ℝ) ^ 3) * (4 * Real.log X ^ 5) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hp (by positivity)
      · exact hl
      · positivity
      · positivity
    _ ≤ _ := by
      have he : 0 ≤ (192 * (max M 0) ^ 4 * D ^ 2) *
          (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by positivity
      dsimp only [R]
      nlinarith only [he]

/-- On the derived theta range, the full weighted power five estimate is equivalent to its
prime only version. This does not assert either OPEN estimate. -/
theorem minor_weighted_prime_iff451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 ≤ ϑ) (hϑ' : ϑ ≤ 1 / 10) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorPrimeWeighted451 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5) := by
  obtain ⟨D, hD, hd⟩ := weighted_prime_defect_family451 hϕ hG ϑ hϑ hϑ'
  constructor
  · rintro ⟨C, hC, hc⟩
    refine ⟨2 * (C + D), by positivity, ?_⟩
    intro X hX η hη hη1 hscale
    have hs := coefficient_split328 (Finset.Icc 1 X)
      (fun N => minorPrimeWeighted451 ϕ G X N ϑ η)
      (fun N => minorWeighted328 ϕ G X N ϑ η)
    have heq : (∑ N ∈ Finset.Icc 1 X,
        ‖minorPrimeWeighted451 ϕ G X N ϑ η - minorWeighted328 ϕ G X N ϑ η‖ ^ 2) =
        ∑ N ∈ Finset.Icc 1 X,
          ‖minorWeighted328 ϕ G X N ϑ η - minorPrimeWeighted451 ϕ G X N ϑ η‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro N hN
      rw [norm_sub_rev]
    rw [heq] at hs
    nlinarith only [hs, hc X hX η hη hη1 hscale, hd X hX η hη hη1 hscale]
  · rintro ⟨C, hC, hc⟩
    refine ⟨2 * (C + D), by positivity, ?_⟩
    intro X hX η hη hη1 hscale
    have hs := coefficient_split328 (Finset.Icc 1 X)
      (fun N => minorWeighted328 ϕ G X N ϑ η)
      (fun N => minorPrimeWeighted451 ϕ G X N ϑ η)
    nlinarith only [hs, hc X hX η hη hη1 hscale, hd X hX η hη hη1 hscale]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.prime_power_family_bounded451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weight_polynomial451
#print axioms LeanLab.BhowmikGrimmelt2026.weighted_defect_power451

#print axioms LeanLab.BhowmikGrimmelt2026.minorPrimeWeighted451

#print axioms LeanLab.BhowmikGrimmelt2026.minorWeighted_sub_prime451

#print axioms LeanLab.BhowmikGrimmelt2026.weighted_prime_defect_family451

#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_prime_iff451

/-
Prime reduction for the full weighted minor family.
Source: P0029 page 4 and page 27 display 7.8.
The uniform discrete multiplier removes the earlier one tenth theta restriction.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.WeightedPrimeDefect451
import LeanLab.BhowmikGrimmelt2026.UniformMinorWeight451

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- Arbitrary bounded multipliers preserve the power five higher prime power defect budget. -/
theorem prime_power_bounded_log5_451 {ϕ : ℝ → ℝ} {M B : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (hB : 0 ≤ B) {X : ℕ} (hX : 2 ≤ X)
    (W : ℕ → ℝ → ℂ) (hW : ∀ N α, ‖W N α‖ ≤ B) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) * W N α‖ ^ 2) ≤
        192 * M ^ 4 * B ^ 2 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hpow : (X : ℝ) ^ 2 * Real.sqrt X ≤ (X : ℝ) ^ (13 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hxp]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ X by exact_mod_cast hX)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by linarith [Real.log_two_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 2
  have hm := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ Real.log (X : ℝ) ^ 3)
  have hlog : Real.log (X : ℝ) ^ 3 ≤ 4 * Real.log X ^ 5 := by
    norm_num at hm
    nlinarith only [hm]
  calc
    _ ≤ 48 * M ^ 4 * B ^ 2 * (X : ℝ) ^ 2 * Real.sqrt X * Real.log X ^ 3 :=
      prime_power_family_bounded451 hM hbound hB hX W hW
    _ = (48 * M ^ 4 * B ^ 2) * ((X : ℝ) ^ 2 * Real.sqrt X) * Real.log X ^ 3 := by ring
    _ ≤ (48 * M ^ 4 * B ^ 2) * (X : ℝ) ^ (13 / 5 : ℝ) * (4 * Real.log X ^ 5) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpow (by positivity)
      · exact hlog
      · positivity
      · positivity
    _ = _ := by ring

/-- Higher prime powers fit the full original weighted budget for every nonnegative theta.
This keeps all allowed eta values and the complete bRhat multiplier. -/
theorem weighted_prime_defect_uniform451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 ≤ ϑ) :
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
  obtain ⟨D, hD, hd⟩ := bRhat_uniform451 hG
  refine ⟨192 * (max M 0) ^ 4 * D ^ 2, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  let R : ℝ := (X : ℝ) ^ ϑ
  have hR : 1 ≤ R := Real.one_le_rpow hx1 hϑ
  let W : ℕ → ℝ → ℂ := fun N α =>
    {α | ¬ MajorArc X R α}.indicator
      (fun α => -bRhat G R (fun q => η * X * q / R) α * ee (-(N * α))) α
  have hW (N : ℕ) (α : ℝ) : ‖W N α‖ ≤ D := by
    by_cases hm : MajorArc X R α
    · simp [W, Set.indicator, hm]
      exact hD.le
    · simpa [W, Set.indicator, hm, norm_mul, ee_eq_library84,
        LeanLab.PNTPort.LargeSieve.norm_e] using hd X R η hR hη hscale α
  have hb := prime_power_bounded_log5_451 (le_max_right M 0) hbound hD.le hX W hW
  simp_rw [minorWeighted_sub_prime451 hG ϕ hX _ ϑ hη]
  apply hb.trans
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hpow : (X : ℝ) ^ (13 / 5 : ℝ) =
      (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hxp]
    congr 1
    norm_num
  rw [hpow]
  have hh : 0 ≤ (192 * (max M 0) ^ 4 * D ^ 2) * ((X : ℝ) ^ ϑ)⁻¹ *
      (X : ℝ) ^ 3 * Real.log X ^ 5 := by positivity
  nlinarith only [hh]

/-- The full weighted power five estimate is equivalent to its prime only version.
This equivalence asserts neither OPEN estimate. -/
theorem minor_weighted_prime_uniform_iff451 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 ≤ ϑ) :
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
  obtain ⟨D, hD, hd⟩ := weighted_prime_defect_uniform451 hϕ hG ϑ hϑ
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
#print axioms LeanLab.BhowmikGrimmelt2026.prime_power_bounded_log5_451
#print axioms LeanLab.BhowmikGrimmelt2026.weighted_prime_defect_uniform451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_weighted_prime_uniform_iff451

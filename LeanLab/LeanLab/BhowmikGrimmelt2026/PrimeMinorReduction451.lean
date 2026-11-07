/-
Exact removal of higher prime powers from the bare minor family.
Source: P0029 page 4 before display 2.1 and page 27 display 7.8.
The equivalence below leaves the prime minor estimate OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.PrimePowerMinor451
import LeanLab.BhowmikGrimmelt2026.Decomp451a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The bare minor coefficient restricted to primes, with the original smoothing and phase. -/
noncomputable def minorPrime451 (ϕ : ℝ → ℝ) (X N : ℕ) (ϑ : ℝ) : ℂ := by
  classical
  exact ∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
    primeSphi451 ϕ N α ^ 2 * ee (-(N * α))

/-- The exact coefficient difference has a multiplier bounded by one. -/
theorem minorBare_sub_prime451 (ϕ : ℝ → ℝ) (X N : ℕ) (ϑ : ℝ) :
    minorBare328 ϕ X N ϑ - minorPrime451 ϕ X N ϑ =
      ∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) *
        {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => ee (-(N * α))) α := by
  classical
  let P : ℝ → Prop := MajorArc X ((X : ℝ) ^ ϑ)
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hs : MeasurableSet {α | ¬ P α} :=
    (measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)).compl
  have hi (u : ℝ → ℂ) (hu : Continuous u) :
      IntervalIntegrable (fun α => if P α then 0 else u α) volume 0 1 := by
    have heq : {α | ¬ P α}.indicator u = (fun α => if P α then 0 else u α) := by
      funext α
      by_cases hp : P α <;> simp [Set.indicator, hp]
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    rw [← heq]
    exact hu.integrableOn_Ioc.indicator hs
  have hf := hi (fun α => Sphi ϕ N α ^ 2 * ee (-(N * α)))
    (((continuous_Sphi ϕ N).pow 2).mul he)
  have hg := hi (fun α => primeSphi451 ϕ N α ^ 2 * ee (-(N * α)))
    ((((continuous_prime_parts451 ϕ N).1).pow 2).mul he)
  unfold minorBare328 minorPrime451
  rw [← intervalIntegral.integral_sub hf hg]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases hp : MajorArc X ((X : ℝ) ^ ϑ) α <;> simp [P, Set.indicator, hp] <;> ring

/-- The exact difference between the two minor families fits the printed power five budget.
No prime minor moment hypothesis is used. -/
theorem minor_prime_defect_family451 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ - minorPrime451 ϕ X N ϑ‖ ^ 2 ≤
        D * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hbound : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left _ _)
  refine ⟨192 * (max M 0) ^ 4, by positivity, ?_⟩
  intro X hX
  let W : ℕ → ℝ → ℂ := fun N α =>
    {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator (fun α => ee (-(N * α))) α
  have hW (N : ℕ) (α : ℝ) : ‖W N α‖ ≤ 1 := by
    by_cases hp : MajorArc X ((X : ℝ) ^ ϑ) α
    · simp [W, Set.indicator, hp]
    · simp only [W, Set.indicator_of_mem (show α ∈ {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α} from hp)]
      rw [ee_eq_library84, LeanLab.PNTPort.LargeSieve.norm_e]
  have hb := prime_power_family_log5_451 (le_max_right M 0) hbound hX W hW
  simp_rw [minorBare_sub_prime451] 
  apply hb.trans
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hpow : (X : ℝ) ^ (13 / 5 : ℝ) =
      (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hxp]
    congr 1
    norm_num
  rw [hpow]
  have hh : 0 ≤ (192 * (max M 0) ^ 4) * ((X : ℝ) ^ ϑ)⁻¹ *
      (X : ℝ) ^ 3 * Real.log X ^ 5 := by positivity
  nlinarith only [hh]

/-- The bare power five estimate is equivalent to its prime only version.
This proves an equivalence and does not assert either OPEN estimate. -/
theorem minor_bare_prime_iff451 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorPrime451 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5) := by
  obtain ⟨D, hD, hd⟩ := minor_prime_defect_family451 hϕ ϑ
  constructor
  · rintro ⟨C, hC, hc⟩
    refine ⟨2 * (C + D), by positivity, ?_⟩
    intro X hX
    have hs := coefficient_split328 (Finset.Icc 1 X)
      (fun N => minorPrime451 ϕ X N ϑ) (fun N => minorBare328 ϕ X N ϑ)
    have heq : (∑ N ∈ Finset.Icc 1 X,
        ‖minorPrime451 ϕ X N ϑ - minorBare328 ϕ X N ϑ‖ ^ 2) =
        ∑ N ∈ Finset.Icc 1 X,
          ‖minorBare328 ϕ X N ϑ - minorPrime451 ϕ X N ϑ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro N hN
      rw [norm_sub_rev]
    rw [heq] at hs
    nlinarith only [hs, hc X hX, hd X hX]
  · rintro ⟨C, hC, hc⟩
    refine ⟨2 * (C + D), by positivity, ?_⟩
    intro X hX
    have hs := coefficient_split328 (Finset.Icc 1 X)
      (fun N => minorBare328 ϕ X N ϑ) (fun N => minorPrime451 ϕ X N ϑ)
    nlinarith only [hs, hc X hX, hd X hX]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minorPrime451
#print axioms LeanLab.BhowmikGrimmelt2026.minorBare_sub_prime451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_prime_defect_family451
#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_prime_iff451

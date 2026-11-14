import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Elementary bookkeeping for P0014 page 39, display 4.32.
The finite zero window permits termwise comparison without a sampling estimate.
These supplies use any complex valued profile and require no critical line hypothesis.
They do not assert the discrete Plancherel estimate of the older split.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp517a
open Real ZeroCount1623

/-- Pull the height out of the squared profile mass on the middle zero window.
Derived bookkeeping for display 4.32 on page 39. -/
theorem moment_height_pullout (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (F : ℂ → ℂ) (T : ℝ) :
    (∑' ρ : ZeroIdx χ T,
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          |ρ.val.im| * ‖F ρ.val‖ ^ 2) ρ) ≤
      T * (∑' ρ : ZeroIdx χ T,
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
          (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖F ρ.val‖ ^ 2) ρ) := by
  classical
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_zeroIdx χ T _) (summable_zeroIdx χ T _)
  intro ρ
  by_cases hρ : ρ ∈ {ρ : ZeroIdx χ T | |ρ.val.im| ≤ 1}ᶜ
  · simp only [Set.indicator_of_mem hρ]
    have h := mul_le_mul_of_nonneg_right ρ.property.2.2.2
      (mul_nonneg (Nat.cast_nonneg
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val))
        (sq_nonneg ‖F ρ.val‖))
    nlinarith only [h]
  · simp only [Set.indicator_of_notMem hρ, mul_zero, le_refl]

/-- Removing the unit height cutoff increases the nonnegative squared profile mass.
Derived bookkeeping for display 4.32 on page 39. -/
theorem moment_indicator_le_full (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (F : ℂ → ℂ) (T : ℝ) :
    (∑' ρ : ZeroIdx χ T,
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖F ρ.val‖ ^ 2) ρ) ≤
    ∑' ρ : ZeroIdx χ T,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖F ρ.val‖ ^ 2 := by
  classical
  apply Summable.tsum_le_tsum _ (summable_zeroIdx χ T _) (summable_zeroIdx χ T _)
  intro ρ
  by_cases hρ : ρ ∈ {ρ : ZeroIdx χ T | |ρ.val.im| ≤ 1}ᶜ
  · simp only [Set.indicator_of_mem hρ, le_refl]
  · simp only [Set.indicator_of_notMem hρ]
    positivity

/-- The middle window is empty at and below height one.
Derived boundary case of the window in display 4.32 on page 39. -/
theorem middle_moment_zero_of_le_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (F : ℂ → ℂ) (T : ℝ) (hT : T ≤ 1) :
    (∑' ρ : ZeroIdx χ T,
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          |ρ.val.im| * ‖F ρ.val‖ ^ 2) ρ) = 0 := by
  classical
  calc
    _ = ∑' _ρ : ZeroIdx χ T, (0 : ℝ) := by
      apply tsum_congr
      intro ρ
      apply Set.indicator_of_notMem
      simpa using ρ.property.2.2.2.trans hT
    _ = 0 := tsum_zero

end LeanLab.HelfgottMajor.Decomp517a

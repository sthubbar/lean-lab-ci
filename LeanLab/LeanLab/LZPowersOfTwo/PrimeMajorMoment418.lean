/-
P0079 page 9, the prime second moment used in the J3 Cauchy Schwarz estimate.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.ScaledMoment396
import LeanLab.LZPowersOfTwo.MajorErrors418

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, J3 before display 36. The shrinking major-arc prime
second moment is bounded by a complete period and Chebyshev's estimate. -/
theorem prime_major_moment418 (ε l : ℝ) (hl : l ≠ 0) :
    ∀ᶠ X : ℝ in atTop,
      (∫ α in major293 X, ‖primeSum293 ε X (l * α)‖ ^ 2) ≤
        (log 4 / |l|) * X * log X := by
  have hl0 : 0 < |l| := abs_pos.mpr hl
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually
    (eventually_ge_atTop (max 1 (2 * |l|))), eventually_ge_atTop (2 : ℝ)] with X hP hX
  let P := X ^ (1 / 3 : ℝ)
  let r := 1 / (2 * |l|)
  have hX0 : 0 < X := by linarith
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP
  have hPl : 2 * |l| ≤ P := (le_max_right _ _).trans hP
  have hP0 : 0 < P := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hP3 : P ^ 3 = X := by
    dsimp [P]
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  have hwidth : P / X ≤ r := by
    apply (div_le_div_iff₀ hX0 (by positivity : 0 < 2 * |l|)).mpr
    have hsq : 2 * |l| ≤ P ^ 2 := by nlinarith
    calc
      P * (2 * |l|) ≤ P * P ^ 2 := mul_le_mul_of_nonneg_left hsq hP0.le
      _ = 1 * X := by nlinarith only [hP3]
  have hsub : major293 X ⊆ Set.Icc (-r) r := by
    intro α hα
    apply abs_le.mp
    exact hα.trans hwidth
  have hc : Continuous (fun α : ℝ => ‖primeSum293 ε X (l * α)‖ ^ 2) := by
    unfold primeSum293 character293
    fun_prop
  calc
    _ ≤ ∫ α in Set.Icc (-r) r, ‖primeSum293 ε X (l * α)‖ ^ 2 :=
      setIntegral_mono_set hc.integrableOn_Icc (Eventually.of_forall (fun α => sq_nonneg _))
        (Eventually.of_forall (fun α hα => hsub hα))
    _ = (1 / |l|) * (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), ‖primeSum293 ε X α‖ ^ 2) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
      have H := prime_scaled_moment_unit396 ε X l (-r) hl
      have he : -r + 1 / |l| = r := by dsimp [r]; ring
      rw [he] at H
      rw [H, prime_second_moment353]
    _ ≤ (1 / |l|) * (log 4 * X * log X) := mul_le_mul_of_nonneg_left
      (prime_second_moment_le353 ε X hX) (by positivity)
    _ = _ := by ring

end LeanLab.LZPowersOfTwo

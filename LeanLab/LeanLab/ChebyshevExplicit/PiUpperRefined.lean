/-
AI wrote the Lean code. Codex task04, 2026-10-21.
Integrate the smaller quadratic error from Psi30Refined.
All bounds are derived from local proofs and Mathlib's Abel identity.
Goldbach is open.
-/
import LeanLab.ChebyshevExplicit.Psi30Refined

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- Integrate the refined theta bound, including its linear logarithmic error. -/
theorem integral_theta_le_110556_refined {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in 2..x, θ t / (t * log t ^ 2) ≤
      1.10556 * (4 * x / log x ^ 2 + x.sqrt / log 2 ^ 2)
        + 5 / (2 * log 6) * (log x - log 2)
        + 5 / 2 * (log (log x) - log (log 2))
        + 10 * (1 / log 2 - 1 / log x) := by
  have h6 : log (6 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  have hi1 := intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2)
    (by linarith : 1 < x)
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ x)] at ht
    exact (continuousAt_id.inv₀ (by dsimp; linarith [ht.1])).continuousWithinAt
  have hi3 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / log t)
      MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ x)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlt : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hi4 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / log t ^ 2)
      MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ x)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlt : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  calc
    _ ≤ ∫ t in 2..x, 1.10556 * (1 / log t ^ 2)
        + 5 / (2 * log 6) * t⁻¹ + 5 / 2 * (t⁻¹ / log t)
        + 10 * (t⁻¹ / log t ^ 2) := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_
        ((((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)).add
          (hi4.const_mul _)) ?_
      · rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith),
          ← integrableOn_Icc_iff_integrableOn_Ioc]
        exact integrableOn_theta_div_id_mul_log_sq x
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hlt : 0 < log t := log_pos (by linarith [ht.1])
        calc θ t / (t * log t ^ 2)
            ≤ (1.10556 * t + 5 / (2 * log 6) * log t ^ 2 + 5 / 2 * log t + 10)
                / (t * log t ^ 2) :=
              div_le_div_of_nonneg_right (theta_le_110556_refined_real ht.1)
                (by positivity)
          _ = _ := by field_simp
    _ = 1.10556 * (∫ t in 2..x, 1 / log t ^ 2)
        + 5 / (2 * log 6) * (log x - log 2)
        + 5 / 2 * (log (log x) - log (log 2))
        + 10 * (1 / log 2 - 1 / log x) := by
      rw [intervalIntegral.integral_add
          (((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _))
          (hi4.const_mul _),
        intervalIntegral.integral_add ((hi1.const_mul _).add (hi2.const_mul _))
          (hi3.const_mul _),
        intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
      rw [integral_inv_of_pos (by norm_num) (by linarith),
        integral_inv_div_log (by norm_num) (by linarith),
        integral_inv_div_log_sq (by norm_num) (by linarith),
        log_div (by linarith : x ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      simp [one_div]
    _ ≤ _ := by
      gcongr
      exact integral_one_div_log_sq_le hx

/-- The smaller main coefficient and recurrence error in the explicit pi bound. -/
theorem pi_le_110556_refined_real {x : ℝ} (hx : 4 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      1.10556 * x / log x + 4.42224 * x / log x ^ 2
        + 1.10556 * x.sqrt / log 2 ^ 2 + 5 / log 6 * log x
        - 5 / (2 * log 6) * log 2
        + 5 / 2 * (1 + log (log x) - log (log 2)) + 10 / log 2 := by
  have hl : 0 < log x := log_pos (by linarith)
  have h2 : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  have h6 : log (6 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  calc
    _ = θ x / log x + ∫ t in 2..x, θ t / (t * log t ^ 2) :=
      primeCounting_eq_theta_div_log_add_integral (by linarith)
    _ ≤ (1.10556 * x + 5 / (2 * log 6) * log x ^ 2 + 5 / 2 * log x + 10)
          / log x
        + (1.10556 * (4 * x / log x ^ 2 + x.sqrt / log 2 ^ 2)
          + 5 / (2 * log 6) * (log x - log 2)
          + 5 / 2 * (log (log x) - log (log 2))
          + 10 * (1 / log 2 - 1 / log x)) :=
      add_le_add
        (div_le_div_of_nonneg_right (theta_le_110556_refined_real (by linarith)) hl.le)
        (integral_theta_le_110556_refined hx)
    _ = _ := by field_simp; ring

/-- The refined explicit bound at every natural input at least four. -/
theorem pi_le_110556_refined (n : ℕ) (hn : 4 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤
      1.10556 * n / log n + 4.42224 * n / log n ^ 2
        + 1.10556 * (n : ℝ).sqrt / log 2 ^ 2 + 5 / log 6 * log n
        - 5 / (2 * log 6) * log 2
        + 5 / 2 * (1 + log (log n) - log (log 2)) + 10 / log 2 := by
  have hx : (4 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Nat.floor_natCast] using pi_le_110556_refined_real hx

end LeanLab.ChebyshevExplicit

/-
AI wrote the Lean code. Codex task04, 2026-10-21.
Abel summation with the zero-constant quadratic theta error.
Keep the reciprocal-log-square integral explicit until choosing a split point.
Goldbach is open.
-/
import LeanLab.ChebyshevExplicit.Psi30Quadratic

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- Integrate the strongest theta error, leaving the leading integral explicit. -/
theorem integral_theta_le_110556_quadratic {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, θ t / (t * log t ^ 2) ≤
      1.10556 * (∫ t in 2..x, 1 / log t ^ 2)
        + 5 / (4 * log 6) * (log x - log 2)
        + 5 / 4 * (log (log x) - log (log 2)) := by
  have h6 : log (6 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  have hi1 := intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2)
    (by linarith : 1 < x)
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact (continuousAt_id.inv₀ (by dsimp; linarith [ht.1])).continuousWithinAt
  have hi3 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / log t)
      MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlt : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  calc
    _ ≤ ∫ t in 2..x, 1.10556 * (1 / log t ^ 2)
        + 5 / (4 * log 6) * t⁻¹ + 5 / 4 * (t⁻¹ / log t) := by
      refine intervalIntegral.integral_mono_on hx ?_
        (((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)) ?_
      · rw [intervalIntegrable_iff, Set.uIoc_of_le hx,
          ← integrableOn_Icc_iff_integrableOn_Ioc]
        exact integrableOn_theta_div_id_mul_log_sq x
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hlt : 0 < log t := log_pos (by linarith [ht.1])
        calc θ t / (t * log t ^ 2)
            ≤ (1.10556 * t + 5 / (4 * log 6) * log t ^ 2 + 5 / 4 * log t)
                / (t * log t ^ 2) :=
              div_le_div_of_nonneg_right (theta_le_110556_quadratic_real ht.1)
                (by positivity)
          _ = _ := by field_simp
    _ = _ := by
      rw [intervalIntegral.integral_add ((hi1.const_mul _).add (hi2.const_mul _))
          (hi3.const_mul _),
        intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
      rw [integral_inv_of_pos (by norm_num) (by linarith),
        integral_inv_div_log (by norm_num) (by linarith),
        log_div (by linarith : x ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]

/-- Abel summation with the strongest error and an unevaluated leading integral. -/
theorem pi_le_110556_integral {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      1.10556 * x / log x + 1.10556 * (∫ t in 2..x, 1 / log t ^ 2)
        + 5 / (2 * log 6) * log x - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log (log x) - log (log 2)) := by
  have hl : 0 < log x := log_pos (by linarith)
  have h6 : log (6 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  calc
    _ = θ x / log x + ∫ t in 2..x, θ t / (t * log t ^ 2) :=
      primeCounting_eq_theta_div_log_add_integral hx
    _ ≤ (1.10556 * x + 5 / (4 * log 6) * log x ^ 2 + 5 / 4 * log x) / log x
        + (1.10556 * (∫ t in 2..x, 1 / log t ^ 2)
          + 5 / (4 * log 6) * (log x - log 2)
          + 5 / 4 * (log (log x) - log (log 2))) :=
      add_le_add (div_le_div_of_nonneg_right (theta_le_110556_quadratic_real hx) hl.le)
        (integral_theta_le_110556_quadratic hx)
    _ = _ := by field_simp; ring

/-- The square-root split with the strongest smaller error polynomial. -/
theorem pi_le_110556_quadratic_real {x : ℝ} (hx : 4 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      1.10556 * x / log x + 4.42224 * x / log x ^ 2
        + 1.10556 * x.sqrt / log 2 ^ 2 + 5 / (2 * log 6) * log x
        - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log (log x) - log (log 2)) := by
  have h := pi_le_110556_integral (by linarith : 2 ≤ x)
  have hj := mul_le_mul_of_nonneg_left (integral_one_div_log_sq_le hx)
    (by norm_num : (0 : ℝ) ≤ 1.10556)
  calc
    _ ≤ 1.10556 * x / log x + 1.10556 * (4 * x / log x ^ 2 + x.sqrt / log 2 ^ 2)
        + 5 / (2 * log 6) * log x - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log (log x) - log (log 2)) := by linarith
    _ = _ := by ring

/-- Split the reciprocal-log-square integral at any valid real point. -/
theorem integral_one_div_log_sq_le_split {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∫ t in 2..x, 1 / log t ^ 2 ≤ (y - 2) / log 2 ^ 2 + (x - y) / log y ^ 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := y)]
  · exact add_le_add (integral_one_div_log_sq_le_mono hy (by norm_num))
      (integral_one_div_log_sq_le_mono hyx (by linarith))
  all_goals apply intervalIntegrable_one_div_log_sq <;> linarith

/-- A fully explicit pi bound for any valid selected split point. -/
theorem pi_le_110556_split {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      1.10556 * x / log x + 1.10556 * ((y - 2) / log 2 ^ 2 + (x - y) / log y ^ 2)
        + 5 / (2 * log 6) * log x - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log (log x) - log (log 2)) := by
  have h := pi_le_110556_integral (hy.trans hyx)
  have hj := mul_le_mul_of_nonneg_left (integral_one_div_log_sq_le_split hy hyx)
    (by norm_num : (0 : ℝ) ≤ 1.10556)
  linarith

end LeanLab.ChebyshevExplicit

import LeanLab.GoldbachGaps.Decomp1520
import LeanLab.GoldbachGaps.Goldston1990Selberg

/-!
P0030 Goldston 1990, display 2 and the Section 5 variance argument.
These are supporting estimates for the trapezoid route recorded in PROGRESS.md.
They do not supply variance control at half width.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset Filter MeasureTheory

/-- Display 2 is nonnegative when its upper endpoint is at least one. -/
theorem jg_nonneg {N : ℝ} (hN : 1 ≤ N) (h : ℝ) : 0 ≤ Jg N h := by
  exact intervalIntegral.integral_nonneg hN (fun x _ => sq_nonneg _)

/-- Display 2 increases with its upper integration endpoint, with width fixed. -/
theorem jg_mono_upper {M N : ℝ} (hM : 1 ≤ M) (hMN : M ≤ N) (h : ℝ) :
    Jg M h ≤ Jg N h := by
  exact intervalIntegral.integral_mono_interval le_rfl hM hMN
    (Eventually.of_forall fun _ => sq_nonneg _)
    (LeanLab.GoldbachGaps.Decomp1520.jg_integrand_integrable h 1 N)

/-- A smaller nonnegative width has a crude bound with an explicit square size error. -/
theorem jg_small_width_le {N h K : ℝ} (hN : 1 ≤ N) (hh : 0 ≤ h) (hhK : h ≤ K) :
    Jg N h ≤ 2 * Jg N K + 2 * K ^ 2 * (N - 1) := by
  have hpt : ∀ x : ℝ, (θ (x + h) - θ x - h) ^ 2 ≤
      2 * (θ (x + K) - θ x - K) ^ 2 + 2 * K ^ 2 := by
    intro x
    have hlo := theta_mono (show x ≤ x + h by linarith)
    have hhi := theta_mono (show x + h ≤ x + K by linarith)
    by_cases hz : 0 ≤ θ (x + h) - θ x - h
    · have he : θ (x + h) - θ x - h ≤ (θ (x + K) - θ x - K) + K := by linarith
      have hs := mul_self_le_mul_self hz he
      nlinarith [sq_nonneg (θ (x + K) - θ x - K - K)]
    · have he : -(θ (x + h) - θ x - h) ≤ K := by linarith
      have hs := mul_self_le_mul_self (show 0 ≤ -(θ (x + h) - θ x - h) by linarith) he
      nlinarith [sq_nonneg (θ (x + K) - θ x - K)]
  have hi := intervalIntegral.integral_mono_on hN
    (LeanLab.GoldbachGaps.Decomp1520.jg_integrand_integrable h 1 N)
    (((LeanLab.GoldbachGaps.Decomp1520.jg_integrand_integrable K 1 N).const_mul 2).add
      intervalIntegrable_const) (fun x _ => hpt x)
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  · change Jg N h ≤ 2 * Jg N K + (N - 1) • (2 * K ^ 2) at hi
    simpa only [smul_eq_mul, mul_comm (N - 1)] using hi
  · exact (LeanLab.GoldbachGaps.Decomp1520.jg_integrand_integrable K 1 N).const_mul 2
  · exact intervalIntegrable_const

/-- Cauchy bounds the discrete reflected covariance by the two variances. -/
theorem reflected_window_covariance_le (N K h : ℕ) (hN : 1 ≤ N) :
    |∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ m - K) *
      (θ (((N - m : ℕ) : ℝ) + h) - θ (N - m : ℕ) - h)| ≤
      Real.sqrt (Jg N K) * Real.sqrt (Jg N h) := by
  rw [← Real.sqrt_mul (jg_nonneg (by exact_mod_cast hN) (K : ℝ))]
  apply Real.abs_le_sqrt
  rw [jg_eq_sum hN, jg_eq_sum hN]
  let f : ℕ → ℝ := fun m => θ ((m : ℝ) + K) - θ m - K
  let g : ℕ → ℝ := fun m => θ ((m : ℝ) + h) - θ m - h
  change (∑ m ∈ Ico 1 N, f m * g (N - m)) ^ 2 ≤
    (∑ m ∈ Ico 1 N, f m ^ 2) * (∑ m ∈ Ico 1 N, g m ^ 2)
  have hr : ∑ m ∈ Ico 1 N, g (N - m) ^ 2 = ∑ m ∈ Ico 1 N, g m ^ 2 := by
    simpa using (Finset.sum_Ico_reflect (fun m => g m ^ 2) 1
      (n := N) (m := N) (by omega))
  have hc := sum_mul_sq_le_sq_mul_sq (Ico 1 N) f (fun m => g (N - m))
  rwa [hr] at hc

end LeanLab.GoldbachGaps.Goldston1990

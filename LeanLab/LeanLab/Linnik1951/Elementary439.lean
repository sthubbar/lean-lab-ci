/-
P0093 page 154 equation 2.2 and page 166 equation 9.3.
Elementary supplies for existing split leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357g
import LeanLab.Linnik1951.Asymptotics357

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

/-- P0093 page 154 equation 2.2, elementary integer phase integral.
Exact integral_exp_two_pi_mul_int357 statement, using the proved lab
phase integral already used for the page 162 Fourier coefficient identity. -/
theorem integral_exp_two_pi_mul_int_proved439 (m : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      Complex.exp (((2 * Real.pi * α * (m : ℝ)) : ℝ) * Complex.I)) =
      if m = 0 then 1 else 0 := by
  convert LeanLab.Perelli1996.Parseval103.integral_e_int m using 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro α hα
  unfold LeanLab.Perelli1996.Kernel.e
  congr 1
  push_cast
  ring

/-- P0093 page 166 equation 9.3, absorption of the logarithm by a
positive power saving. Exact log_power_absorption357 statement. -/
theorem log_power_absorption_proved439 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      Real.log (N : ℝ) ^ 13 ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (13 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 40)).def (by norm_num : (0 : ℝ) < 1)
  have he : ∀ᶠ (N : ℕ) in atTop,
      ‖Real.log (N : ℝ) ^ (13 : ℝ)‖ ≤ 1 * ‖(N : ℝ) ^ (1 / 40 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hh
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp he
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl := Real.log_nonneg hN1
  have h := hN0 N (le_trans (le_max_right _ _) hN.le)
  have hp13 : Real.log (N : ℝ) ^ (13 : ℝ) = Real.log (N : ℝ) ^ (13 : ℕ) :=
    Real.rpow_natCast _ 13
  rw [hp13] at h
  have hb : |Real.log (N : ℝ) ^ 13| ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
    simpa only [Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), one_mul] using h
  exact (le_abs_self _).trans hb

end LeanLab.Linnik1951

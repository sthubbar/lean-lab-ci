/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
An eventual comparison for the error and the rounded sieve cutoff.
-/
import Mathlib

namespace LeanLab.Routes.Task59

open Real Filter Topology

/-- A log cubed error and a square root cutoff are negligible at log squared scale. -/
theorem eventually_error15_small (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / log N ^ 3 + sqrt N + 2 ≤ ε * (N : ℝ) / log N ^ 2 := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ‖log (N : ℝ) ^ (2 : ℝ)‖ ≤ ε / 6 * ‖(N : ℝ) ^ (1 / 2 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).bound
        (by positivity : 0 < ε / 6))
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 * C / ε + 1 ≤ log (N : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hsmall, hlarge, eventually_ge_atTop 2] with N hs hl hN
  let x : ℝ := N
  let L : ℝ := log x
  have hx2 : 2 ≤ x := by
    change (2 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := log_pos (by linarith)
  change ‖L ^ (2 : ℝ)‖ ≤ ε / 6 * ‖x ^ (1 / 2 : ℝ)‖ at hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL.le _),
    abs_of_pos (Real.rpow_pos_of_pos hx0 _),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hs
  norm_num only [Nat.cast_ofNat] at hs
  rw [← Real.sqrt_eq_rpow] at hs
  change 2 * C / ε + 1 ≤ L at hl
  have hCL : C ≤ ε / 2 * L := by
    have hc' : 2 * C / ε ≤ L := by linarith
    rw [div_le_iff₀ hε] at hc'
    nlinarith
  have hterm : C * x / L ^ 3 ≤ (ε / 2 * x) / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc C * x * L ^ 2 ≤ (ε / 2 * L) * x * L ^ 2 := by gcongr
      _ = (ε / 2 * x) * L ^ 3 := by ring
  have hsqrt : sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hcut : sqrt x + 2 ≤ (ε / 2 * x) / L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc (sqrt x + 2) * L ^ 2 ≤ (sqrt x + 2) * (ε / 6 * sqrt x) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = ε / 6 * ((sqrt x) ^ 2 + 2 * sqrt x) := by ring
      _ = ε / 6 * (x + 2 * sqrt x) := by rw [Real.sq_sqrt hx0.le]
      _ ≤ ε / 6 * (x + 2 * x) := by gcongr
      _ = ε / 2 * x := by ring
  change C * x / L ^ 3 + sqrt x + 2 ≤ ε * x / L ^ 2
  calc C * x / L ^ 3 + sqrt x + 2 = C * x / L ^ 3 + (sqrt x + 2) := by ring
    _ ≤ (ε / 2 * x) / L ^ 2 + (ε / 2 * x) / L ^ 2 := add_le_add hterm hcut
    _ = ε * x / L ^ 2 := by ring

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.eventually_error15_small

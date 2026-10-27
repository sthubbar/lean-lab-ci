/-
P0087 Akeno 2026 page 5, U = V = X to power one third.
Exact scale and exponent arithmetic for equations 7 and 8.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Akeno2026.Balance86
open Real
/-- LEAF. Page 5 balanced Type II scales with explicit comparability constant four. -/
theorem balanced_scales {X M N : ℝ} (hX : 1 ≤ X)
    (hM : X ^ ((1 : ℝ) / 3) ≤ M) (hN : X ^ ((1 : ℝ) / 3) ≤ N)
    (hMN : M * N ≤ 4 * X) :
    M ≤ 4 * X ^ ((2 : ℝ) / 3) ∧ N ≤ 4 * X ^ ((2 : ℝ) / 3) := by
  have hX0 : 0 < X := by linarith
  have hp : 0 < X ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hX0 _
  have hm0 : 0 ≤ M := by linarith
  have hn0 : 0 ≤ N := by linarith
  have hid : X ^ ((2 : ℝ) / 3) * X ^ ((1 : ℝ) / 3) = X := by
    rw [← Real.rpow_add hX0]
    norm_num
  constructor
  · have hh := mul_le_mul_of_nonneg_left hN hm0
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hM hn0
    nlinarith
/-- LEAF. Page 5 equation 7, the Type I scale term at U V = X to power two thirds. -/
theorem typeI_scale_term {X D M : ℝ} (hX : 0 < X) (hM : M ≤ X ^ ((2 : ℝ) / 3)) :
    M * D ^ 2 / X ≤ D ^ 2 * X ^ (-(1 : ℝ) / 3) := by
  have hr : X ^ ((2 : ℝ) / 3) / X = X ^ (-(1 : ℝ) / 3) := by
    calc
      _ = X ^ ((2 : ℝ) / 3) / X ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = X ^ ((2 : ℝ) / 3 - 1) := (Real.rpow_sub hX _ _).symm
      _ = _ := by congr 1; norm_num
  calc
    _ ≤ X ^ ((2 : ℝ) / 3) * D ^ 2 / X :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM (sq_nonneg D)) hX.le
    _ = D ^ 2 * (X ^ ((2 : ℝ) / 3) / X) := by ring
    _ = _ := by rw [hr]
/-- LEAF. Pages 5 to 6 epsilon absorption, after an epsilon over four input estimate. -/
theorem epsilon_absorption {X ε : ℝ} (hX : 0 < X) :
    X ^ (2 + 2 * (ε / 4)) * X ^ (ε / 2) = X ^ (2 + ε) := by
  rw [← Real.rpow_add hX]
  congr 1
  ring

end LeanLab.Akeno2026.Balance86

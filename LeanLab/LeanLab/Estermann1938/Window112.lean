import LeanLab.Estermann1938.Coeff112
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Estermann 1938, P0091, page 313, display 48.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Window112
open Real Filter
open Decomp112 Coeff112

/-- The large n convention in display 1 absorbs the subtraction by three before display 48. -/
theorem scale_eventually (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ (n : ℝ) * Real.log n ^ (-a) := by
  have hlo := (isLittleO_log_rpow_rpow_atTop a (s := 1) one_pos).bound
    (c := (1 : ℝ) / 3) (by norm_num)
  have hh := tendsto_natCast_atTop_atTop.eventually hlo
  filter_upwards [hh, eventually_ge_atTop 3] with n hn h3
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hP : 0 < Real.log n ^ a := Real.rpow_pos_of_pos hL a
  have hN : Real.log n ^ a ≤ (1 / 3 : ℝ) * n := by
    rw [Real.norm_of_nonneg hP.le, Real.rpow_one,
      Real.norm_of_nonneg (Nat.cast_nonneg n)] at hn
    exact hn
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv, le_div_iff₀ hP]
  nlinarith

/-- Display 48 at an explicit scale threshold, before taking n sufficiently large. -/
theorem b_window {n m : ℕ} (hn : 2 ≤ n) (hmn : m ≤ n) (η : ℝ)
    (hscale : 3 ≤ (n : ℝ) * Real.log n ^ (-(η / 3)))
    (hm : 2 * (n : ℝ) * Real.log n ^ (-(η / 3)) ≤ m) :
    (n : ℝ) * Real.log n ^ (-2 - η / 3) ≤ b n m := by
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hnum : (n : ℝ) * Real.log n ^ (-(η / 3)) ≤ (m : ℝ) - 3 := by
    nlinarith
  calc
    (n : ℝ) * Real.log n ^ (-2 - η / 3) =
        ((n : ℝ) * Real.log n ^ (-(η / 3))) / Real.log n ^ 2 := by
      rw [show -2 - η / 3 = -(η / 3) - 2 by ring, Real.rpow_sub hL, Real.rpow_two]
      ring
    _ ≤ ((m : ℝ) - 3) / Real.log n ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ b n m := b_lower hn hmn

/-- Estermann's display 48, page 313, under the paper's η greater than four convention. -/
theorem display48 (η : ℝ) (hη : 4 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      2 * (n : ℝ) * Real.log n ^ (-(η / 3)) ≤ m → m ≤ n →
      (n : ℝ) * Real.log n ^ (-2 - η / 3) ≤ b n m := by
  filter_upwards [scale_eventually (η / 3), eventually_ge_atTop 2] with n hscale hn
  intro m hm hmn
  exact b_window hn hmn η hscale hm

/-- A concrete nonempty instance of the display 48 window at n equal to 64 and η equal to 6. -/
theorem window_instance :
    3 ≤ (64 : ℝ) * Real.log 64 ^ (-((6 : ℝ) / 3)) ∧
    2 * (64 : ℝ) * Real.log 64 ^ (-((6 : ℝ) / 3)) ≤ (64 : ℝ) := by
  have he : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlo : (4 : ℝ) < Real.log 64 := by rw [he]; nlinarith [Real.log_two_gt_d9]
  have hhi : Real.log 64 < (21 : ℝ) / 5 := by rw [he]; nlinarith [Real.log_two_lt_d9]
  norm_num only [show (6 : ℝ) / 3 = 2 by norm_num]
  rw [Real.rpow_neg (by linarith : 0 ≤ Real.log 64), Real.rpow_two]
  constructor
  · rw [← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log 64))]
    nlinarith [sq_nonneg (Real.log 64 - 21 / 5)]
  · rw [← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log 64))]
    nlinarith [sq_nonneg (Real.log 64 - 4)]

#print axioms window_instance

#print axioms scale_eventually
#print axioms b_window
#print axioms display48

end LeanLab.Estermann1938.Window112

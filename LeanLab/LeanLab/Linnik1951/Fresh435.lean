/-
P0093 pages 154 and 166. Exact elementary bridges for remaining cited inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Mass435
import LeanLab.Linnik1951.SPLIT_count_circle_coefficient357
import LeanLab.Linnik1951.SPLIT_exceptional_prime_mass357
import LeanLab.Perelli1996.Parseval103

namespace LeanLab.Linnik1951

/-- P0093 page 154 equation 2.2, the elementary orthogonality step.
Exact integral_exp_two_pi_mul_int357 statement from the already proved
lab phase integral. This does not decompose the blocked tuple identity. -/
theorem integral_exp_two_pi_mul_int_proved435 (m : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      Complex.exp (((2 * Real.pi * α * (m : ℝ)) : ℝ) * Complex.I)) =
      if m = 0 then 1 else 0 := by
  have he (α : ℝ) : Complex.exp (((2 * Real.pi * α * (m : ℝ)) : ℝ) * Complex.I) =
      LeanLab.Perelli1996.Kernel.e ((m : ℝ) * α) := by
    unfold LeanLab.Perelli1996.Kernel.e
    congr 1
    push_cast
    ring
  simp_rw [he]
  exact LeanLab.Perelli1996.Parseval103.integral_e_int m

/-- P0093 page 166 after equation 9.3. Exact
log_power_absorption357 statement from the proved general logarithmic
absorption theorem. There is no analytic input. -/
theorem log_power_absorption_proved435 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      Real.log (N : ℝ) ^ 13 ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
  exact log_power_small435 13 (1 / 40) (by norm_num)

end LeanLab.Linnik1951

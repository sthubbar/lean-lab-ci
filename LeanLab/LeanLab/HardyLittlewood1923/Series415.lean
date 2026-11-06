import LeanLab.HardyLittlewood1923.Decomp276b
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
AI wrote this Lean code for CODEX task415.
P0004 pages 5 and 24 equations 1.31 and 3.141.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Series415

open Real Finset MeasureTheory
open LeanLab.HardyLittlewood1923.Decomp276b

/-- P0004 page 24 before equation 3.141.
The prime series on a fixed positive radius circle is continuous. -/
theorem continuous_prime_circle {n : ℕ} (hn : 0 < n) :
    Continuous (fun θ : ℝ => primeSeries (localY n θ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold primeSeries
  apply continuous_tsum (u := fun m : ℕ => (m : ℝ) * Real.exp (-(1 / (n : ℝ)) * m))
  · intro m
    by_cases hm : m.Prime
    · simp only [if_pos hm]
      unfold localY
      fun_prop
    · simpa only [if_neg hm] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · simpa only [pow_one] using Real.summable_pow_mul_exp_neg_nat_mul 1 (by positivity : 0 < 1 / (n : ℝ))
  · intro m θ
    split_ifs with hm
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg m), Complex.norm_exp]
      have hre : (-(m : ℂ) * localY n θ).re = -(1 / (n : ℝ)) * m := by
        simp [localY]
        ring
      rw [hre]
      exact mul_le_mul_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg m)) (by positivity)
    · simp only [norm_zero]
      positivity

/-- P0004 pages 5 and 24 equations 1.31 and 3.141.
The circle prime series has angular period two pi. -/
theorem periodic_prime_circle (n : ℕ) :
    Function.Periodic (fun θ : ℝ => primeSeries (localY n θ)) (2 * π) := by
  intro θ
  unfold primeSeries
  apply tsum_congr
  intro m
  split_ifs with hm
  · congr 1
    have he : -(m : ℂ) * localY n (θ + 2 * π) =
        -(m : ℂ) * localY n θ + (m : ℂ) * (2 * π * Complex.I) := by
      simp only [localY, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    rw [he, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I]
    simp
  · rfl

/-- P0004 page 24 before equation 3.141.
The square mean integrand on every circle of positive radius is continuous. -/
theorem continuous_prime_square {n : ℕ} (hn : 0 < n) :
    Continuous (fun θ : ℝ => ‖primeSeries (localY n θ)‖ ^ 2) :=
  (continuous_prime_circle hn).norm.pow 2

#print axioms continuous_prime_circle
#print axioms periodic_prime_circle
#print axioms continuous_prime_square

end LeanLab.HardyLittlewood1923.Series415

namespace LeanLab.HardyLittlewood1923.Decomp415a

/-- The squared prime coefficient mass on the circle of radius exp of minus one over n.
P0004 page 24 section 3.14, the Parseval display. -/
noncomputable def primeSquareMass (n : ℕ) : ℝ :=
  ∑' m : ℕ, if m.Prime then Real.log m ^ 2 * Real.exp (-2 * (m : ℝ) / n) else 0

end LeanLab.HardyLittlewood1923.Decomp415a

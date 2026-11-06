import LeanLab.HardyLittlewood1923.Series415
import Mathlib.NumberTheory.Chebyshev

/-!
AI wrote this Lean code for CODEX task415.
P0004 page 24 section 3.14, the damped prime square mass.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Mass415

open Real Finset
open LeanLab.HardyLittlewood1923.Decomp415a

/-- P0004 page 24 section 3.14.
The undamped squared prime coefficients have the required partial sum bound. -/
theorem prime_square_partial_sum {M : ℕ} (hM : 1 ≤ M) :
    (∑ p ∈ Nat.primesLE M, Real.log p ^ 2) ≤
      Real.log 4 * M * Real.log M := by
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE M, Real.log M * Real.log p := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpM, hprime⟩ := Nat.mem_primesLE.mp hp
      have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
      have hle : Real.log p ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpM)
      nlinarith only [mul_le_mul_of_nonneg_right hle hlogp]
    _ = Real.log M * Chebyshev.theta M := by
      rw [Chebyshev.theta_eq_sum_primesLE_log, mul_sum]
    _ ≤ Real.log M * (Real.log 4 * M) :=
      mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (by positivity)) hlogM
    _ = _ := by ring

/-- P0004 page 24 section 3.14, the coefficient sum in Parseval is convergent. -/
theorem prime_square_mass_summable {n : ℕ} (hn : 0 < n) :
    Summable (fun m : ℕ =>
      if m.Prime then Real.log m ^ 2 * Real.exp (-2 * (m : ℝ) / n) else 0) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 2 (by positivity : 0 < 2 / (n : ℝ))
  apply Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity) _ hs
  intro m
  split_ifs with hm
  · rw [show -2 * (m : ℝ) / n = -(2 / (n : ℝ)) * m by ring]
    gcongr
    exact Real.log_le_self (Nat.cast_nonneg m)
  · positivity

/-- P0004 page 24 section 3.14.
The prime coefficient mass is positive since its coefficient at prime two is positive. -/
theorem prime_square_mass_pos {n : ℕ} (hn : 0 < n) :
    0 < primeSquareMass n := by
  have hs := prime_square_mass_summable hn
  have ht := hs.le_tsum 2 (fun m _ => by split_ifs <;> positivity)
  have hp : Nat.Prime 2 := Nat.prime_two
  rw [if_pos hp] at ht
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold primeSquareMass
  exact lt_of_lt_of_le (by positivity) ht

#print axioms prime_square_partial_sum
#print axioms prime_square_mass_summable
#print axioms prime_square_mass_pos

end LeanLab.HardyLittlewood1923.Mass415

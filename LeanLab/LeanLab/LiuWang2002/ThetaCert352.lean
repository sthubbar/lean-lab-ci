import Mathlib

/-!
Finite certificate transfer for Schoenfeld page 356, display 5.1 star.
The base 68 divided by 25 is derived proof data.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task352
open Real

/-- The derived rational base is below the exponential of the coefficient
in Schoenfeld page 356, display 5.1 star. -/
theorem certificate_base : (68 / 25 : ℝ) < exp 1.001093 := by
  have he := Real.exp_one_gt_d9
  have ht := Real.add_one_le_exp (0.001093 : ℝ)
  rw [show (1.001093 : ℝ) = 1 + 0.001093 by norm_num, exp_add]
  nlinarith [exp_pos (0.001093 : ℝ)]

/-- An exact integer primorial certificate implies the theta estimate at
a positive integer endpoint. Derived transfer for page 356, display 5.1 star. -/
theorem theta_of_primorial_certificate (n : ℕ) (hn : 0 < n)
    (hcert : primorial n * 25 ^ n < 68 ^ n) :
    Chebyshev.theta n < 1.001093 * n := by
  have hc : (primorial n : ℝ) * 25 ^ n < (68 : ℝ) ^ n := by
    exact_mod_cast hcert
  have hp : (primorial n : ℝ) < (68 / 25 : ℝ) ^ n := by
    rw [div_pow, lt_div_iff₀ (by positivity)]
    exact hc
  have hb := pow_lt_pow_left₀ certificate_base (by norm_num : (0 : ℝ) ≤ 68 / 25)
    (by omega : n ≠ 0)
  have hh : (primorial n : ℝ) < exp (1.001093 * n) := by
    calc
      _ < (exp 1.001093) ^ n := hp.trans hb
      _ = exp (1.001093 * n) := by rw [mul_comm, exp_nat_mul]
  rw [Chebyshev.theta_eq_log_primorial]
  simp only [Nat.floor_natCast]
  exact (log_lt_iff_lt_exp (by exact_mod_cast primorial_pos n)).mpr hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A kernel checked initial certificate through 64 for page 356, display
5.1 star. This checks only 63 reachable integer endpoints. -/
theorem initial_certificate : ∀ n ∈ Finset.Icc 2 64,
    primorial n * 25 ^ n < 68 ^ n := by
  decide +kernel

/-- The initial real interval of the finite leaf on page 356, display
5.1 star. This includes all positive endpoints through 64. -/
theorem theta_initial (X : ℝ) (hX : 0 < X) (h64 : X ≤ 64) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases h2 : X < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two h2]
    positivity
  · have hf2 : 2 ≤ Nat.floor X := by exact Nat.le_floor (show (2 : ℝ) ≤ X from le_of_not_gt h2)
    have hf64 : Nat.floor X ≤ 64 := Nat.floor_le_of_le h64
    have hn := theta_of_primorial_certificate (Nat.floor X) (by omega)
      (initial_certificate _ (Finset.mem_Icc.mpr ⟨hf2, hf64⟩))
    rw [Chebyshev.theta_eq_theta_coe_floor]
    exact hn.trans_le (mul_le_mul_of_nonneg_left (Nat.floor_le hX.le) (by norm_num))

end LeanLab.LiuWang2002.Task352

#print axioms LeanLab.LiuWang2002.Task352.certificate_base
#print axioms LeanLab.LiuWang2002.Task352.theta_of_primorial_certificate
#print axioms LeanLab.LiuWang2002.Task352.initial_certificate
#print axioms LeanLab.LiuWang2002.Task352.theta_initial

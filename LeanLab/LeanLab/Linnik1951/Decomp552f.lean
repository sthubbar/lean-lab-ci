/-
P0093 page 159 before equation 5.3. The crude prime square mass route.
This bound is linear and does not reach the requested local error scale.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp552d
import LeanLab.Linnik1951.Principal442

namespace LeanLab.Linnik1951

/-- P0093 page 159 before equation 5.3. Auxiliary crude bound for
the prime square integral on any centred interval of radius at most one
half. Removing the residual phase loses the cancellation needed later. -/
theorem prime_window_crude552 (N : ℕ) (hN : 1 ≤ N)
    (r : ℝ) (hr : 0 ≤ r) (hrh : r ≤ 1 / 2) (n : ℤ) :
    ‖∫ z in -r..r, primeFourier111 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
        2 * (N : ℝ) := by
  have hchar (z : ℝ) : characterPrime280 (1 : DirichletCharacter ℂ 1) N z =
      primeFourier111 N z := by
    unfold characterPrime280 primeFourier111
    apply tsum_congr
    intro p
    rw [show ((p : ℕ) : ZMod 1) = 1 from Subsingleton.elim _ _, map_one, one_mul]
  calc
    _ ≤ ∫ z in -r..r, ‖primeFourier111 N z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ = ∫ z in -r..r, ‖primeFourier111 N z‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro z hz
      simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
    _ ≤ 2 * (N : ℝ) := by
      simpa only [hchar] using character_local_mass442 (1 : DirichletCharacter ℂ 1)
        N hN r hr hrh

/-- P0093 pages 155 and 159 equations 3.1 and 5.3.
Auxiliary crude unit modulus bound. Together with
linear_bound_insufficient552 it records why phase removal alone does
not supply the sealed small residual error estimate. -/
theorem local_arc_unit_crude552 (N : ℕ) (hN : 1 ≤ N)
    (hτ : 2 ≤ (N : ℝ) ^ (1 / 7 : ℝ)) (n : ℤ) :
    ‖localArc1622 N 1 n‖ ≤ 2 * (N : ℝ) := by
  have hr : 0 ≤ 1 / (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hrh : 1 / (N : ℝ) ^ (1 / 7 : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hτ
  simpa [localArc1622] using prime_window_crude552 N hN _ hr hrh n

end LeanLab.Linnik1951

import LeanLab.Halupczok2012.Statements

/-!
Halupczok journal page 333, the numerical hypotheses of Corollary 1.1.
The sealed remainder power bound already implies the second interval power bound.
The weighted sieve input is still required.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Corollary398

/-- Page 332, the remainder power condition implies the missing second interval power bound. -/
theorem second_interval_bound {X1 X2 Y : ℝ} {n : ℕ}
    (hY : 0 ≤ Y) (hYX2 : Y ≤ X2) (hn : X1 + X2 + 2 * Y ≤ n)
    (hp : ((n : ℝ) - X1) ^ (0.933 : ℝ) ≤ Y) :
    X2 ^ (0.933 : ℝ) ≤ Y := by
  exact (Real.rpow_le_rpow (hY.trans hYX2) (by linarith) (by norm_num)).trans hp

/-- Page 332 and page 345, the stronger Corollary 1.1 interval exponents imply both 0.861 bounds. -/
theorem weaker_interval_bounds {X1 X2 Y : ℝ} {n : ℕ}
    (hY : 1 ≤ Y) (hYX1 : Y ≤ X1) (hYX2 : Y ≤ X2) (hn : X1 + X2 + 2 * Y ≤ n)
    (h1 : X1 ^ (0.933 : ℝ) ≤ Y) (h2 : ((n : ℝ) - X1) ^ (0.933 : ℝ) ≤ Y) :
    X1 ^ (0.861 : ℝ) ≤ Y ∧ X2 ^ (0.861 : ℝ) ≤ Y := by
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le (hY.trans hYX1) (by norm_num)).trans h1
  · exact (Real.rpow_le_rpow_of_exponent_le (hY.trans hYX2) (by norm_num)).trans
      (second_interval_bound (by linarith) hYX2 hn h2)

/-- A negative route check for page 345.
Subtracting these global sieve bounds supplies no positive local count. -/
theorem global_subtraction_nonpos {c C X Y : ℝ}
    (hc : 0 < c) (hC : 2 * c ≤ C) (hX : 1 < X) (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    c * (X + Y) / Real.log (X + Y) ^ 2 - C * X / Real.log X ^ 2 ≤ 0 := by
  have hXp : 0 < X := by linarith
  have hCp : 0 < C := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hLY : 0 < Real.log (X + Y) := Real.log_pos (by linarith)
  have hlog : Real.log X ≤ Real.log (X + Y) := Real.log_le_log hXp (by linarith)
  have hden := pow_le_pow_left₀ hL.le hlog 2
  have hnum : c * (X + Y) ≤ C * X := by
    have h1 := mul_le_mul_of_nonneg_left hYX hc.le
    have h2 := mul_le_mul_of_nonneg_right hC hXp.le
    nlinarith
  apply sub_nonpos.mpr
  apply (div_le_div_iff₀ (by positivity : 0 < Real.log (X + Y) ^ 2)
    (by positivity : 0 < Real.log X ^ 2)).mpr
  exact (mul_le_mul_of_nonneg_right hnum (sq_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ C * X))

end LeanLab.Halupczok2012.Corollary398

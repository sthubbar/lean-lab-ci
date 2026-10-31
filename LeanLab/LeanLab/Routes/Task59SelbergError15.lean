/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The square root error estimate for the corrected U1436 choice A equal to 15.
-/
import LeanLab.Routes.Task59Error15

namespace LeanLab.Routes.Task59

/-- Bound the Selberg error after the integral and log cutoff are bounded. -/
theorem selberg_error15_le (x L u v K : ℝ) (hx : 0 ≤ x) (hL : 0 < L)
    (hu : u ≤ x) (hv0 : 0 ≤ v) (hvL : v ≤ L) (hK : 0 ≤ K) :
    Real.sqrt ((x + u) * (Real.exp 126 * v ^ 9) * (K * x / L ^ 15)) ≤
      Real.sqrt (2 * Real.exp 126 * K) * x / L ^ 3 := by
  have hv9 : v ^ 9 ≤ L ^ 9 := pow_le_pow_left₀ hv0 hvL _
  have hc : 0 ≤ K * x / L ^ 15 := by positivity
  have hb : (x + u) * (Real.exp 126 * v ^ 9) ≤
      (2 * x) * (Real.exp 126 * L ^ 9) :=
    mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hv9 (Real.exp_pos _).le)
      (by positivity) (by positivity)
  have hrad : (x + u) * (Real.exp 126 * v ^ 9) * (K * x / L ^ 15) ≤
      (2 * Real.exp 126 * K) * x ^ 2 / L ^ 6 := by
    calc _ ≤ (2 * x) * (Real.exp 126 * L ^ 9) * (K * x / L ^ 15) :=
          mul_le_mul_of_nonneg_right hb hc
      _ = _ := by field_simp [hL.ne'] <;> ring
  calc _ ≤ Real.sqrt ((2 * Real.exp 126 * K) * x ^ 2 / L ^ 6) :=
        Real.sqrt_le_sqrt hrad
    _ = Real.sqrt (2 * Real.exp 126 * K) * x / L ^ 3 := by
        apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
        rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
        ring

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.selberg_error15_le

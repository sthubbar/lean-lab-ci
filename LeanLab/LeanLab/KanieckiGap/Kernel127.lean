/-
P0022, page 362, display 2. The exponential transform of the logarithmic
window gives the elementary kernel appearing at the pole and the zeros.
The contour shift and the sum over zeros remain cited.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.Taper127

namespace LeanLab.KanieckiGap.Kernel127

/-- Page 362, display 2. Integrating the exponential window and dividing
once more by its nonzero complex parameter gives the square denominator. -/
theorem window_transform (L A : ℝ) {z : ℂ} (hz : z ≠ 0) :
    (∫ t in L..A, Complex.exp (z * t) / z) =
      (Complex.exp (z * A) - Complex.exp (z * L)) / z ^ 2 := by
  rw [intervalIntegral.integral_div, integral_exp_mul_complex hz]
  ring

/-- Page 362, display 2. The normalized exponential window equals
 the modified Selberg kernel at any nonzero complex argument. -/
theorem selberg_kernel {x a : ℝ} (hx : 1 < x) (_ha : 1 < a)
    {z : ℂ} (hz : z ≠ 0) :
    (∫ t in Real.log x..a * Real.log x, Complex.exp (z * t) / z) /
        (((a - 1) * Real.log x : ℝ) : ℂ) =
      ((x : ℂ) ^ ((a : ℂ) * z) - (x : ℂ) ^ z) /
        (z ^ 2 * (((a - 1) * Real.log x : ℝ) : ℂ)) := by
  have hx0 : 0 < x := by linarith
  have hcp (w : ℂ) : (x : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx0.ne'),
      ← Complex.ofReal_log hx0.le]
  have hA : Complex.exp (z * ((a * Real.log x : ℝ) : ℂ)) = (x : ℂ) ^ ((a : ℂ) * z) := by
    rw [hcp]
    congr 1
    push_cast
    ring
  have hL : Complex.exp (z * (Real.log x : ℂ)) = (x : ℂ) ^ z := by
    rw [hcp]
    congr 1
    ring
  rw [window_transform _ _ hz, hA, hL, div_div]

/-- Page 362, display 2. At z equal to one minus s this is exactly
 the pole numerator and square denominator in the paper formula. -/
theorem pole_kernel {x a : ℝ} (hx : 1 < x) (ha : 1 < a)
    {s : ℂ} (hs : s ≠ 1) :
    (∫ t in Real.log x..a * Real.log x, Complex.exp ((1 - s) * t) / (1 - s)) /
        (((a - 1) * Real.log x : ℝ) : ℂ) =
      ((x : ℂ) ^ ((a : ℂ) * (1 - s)) - (x : ℂ) ^ (1 - s)) /
        ((1 - s) ^ 2 * (((a - 1) * Real.log x : ℝ) : ℂ)) :=
  selberg_kernel hx ha (sub_ne_zero.mpr hs.symm)

end LeanLab.KanieckiGap.Kernel127

#print axioms LeanLab.KanieckiGap.Kernel127.window_transform
#print axioms LeanLab.KanieckiGap.Kernel127.selberg_kernel
#print axioms LeanLab.KanieckiGap.Kernel127.pole_kernel

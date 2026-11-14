/-
Jia 1996 page 270, exact polynomial certificates for Omega11.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Kernel11_566

namespace LeanLab.Languasco2004.Numeric11_566
open Real Set intervalIntegral Kernel11_566 Numeric548 Numeric30_548
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF. Page 270: exact polynomial integration certifies the logarithmic coefficient with a reserve. -/
theorem logPolynomial_integral :
    (0.0126553 : ℝ) ≤ ∫ t in (17 / 63 : ℝ)..(17 / 57),
      ∫ u in (17 / 30 - 6 / 5 * t)..((1 - t) / 3), logPolynomial t u := by
  simp only [logPolynomial, invPoly3, invPoly5, Midpoint566.invPoly1]
  ring_nf
  simp (config := { maxSteps := 1000000 }) (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (config := { maxSteps := 1000000 }) (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms logPolynomial_integral

/-- Page 270: exact polynomial integration certifies the rational coefficient with a reserve. -/
theorem ratPolynomial_integral :
    (0.01510605 : ℝ) ≤ ∫ t in (17 / 63 : ℝ)..(17 / 57),
      ∫ u in ((1 - t) / 3)..(7 / 24 - t / 8), ratPolynomial t u := by
  unfold ratPolynomial invPoly5
  ring_nf
  simp (config := { maxSteps := 1000000 }) (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  ring_nf
  simp (config := { maxSteps := 1000000 }) (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [integral_add, integral_sub, integral_const_mul (𝕜 := ℝ), integral_mul_const (𝕜 := ℝ),
     integral_pow, integral_const, integral_id, smul_eq_mul]
  norm_num

#print axioms logPolynomial_integral
#print axioms ratPolynomial_integral
end
end LeanLab.Languasco2004.Numeric11_566

/-
Jia 1996 pages 279 and 280, Lemma 26.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
namespace LeanLab.Languasco2004.Source568
/-- Page 280: the six printed remainder coefficients sum exactly. -/
theorem remainder_coefficients :
    (0.005530 + 0.031194 + 0.066046 + 0.050732 + 0.051408 + 0.084400 : ℝ) =
      0.289310 := by norm_num
/-- Pages 279 and 280: the distinguished region and remainder recover the group coefficient. -/
theorem group_coefficients : (0.009636 + 0.289310 : ℝ) = 0.298946 := by norm_num
/-- Page 279: the Omega4 source domain has a strict interior point. -/
theorem region4_interior :
    (41 / 180 : ℝ) < 7 / 30 ∧ (7 / 30 : ℝ) < 8 / 33 ∧
      (41 / 90 - 7 / 30 : ℝ) < 9 / 40 ∧ (9 / 40 : ℝ) < 7 / 30 := by norm_num
#print axioms remainder_coefficients
#print axioms group_coefficients
#print axioms region4_interior
end LeanLab.Languasco2004.Source568

import LeanLab.HelfgottMajor.Contour457
import LeanLab.HelfgottMajor.Numerator457
import LeanLab.HelfgottMajor.LogWeight457

/-!
The two square energies in the principal contour estimate.
Source P0014 pages 34 and 35, displays 4.12 to 4.15.
Neither energy involves a prime sum, a zero sum or the scale x.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

/-- LEAF. P0014 page 35, the first Cauchy Schwarz factor after display 4.13.
At q equal to one, its squared integral is bounded by the printed 226.844.
This leaf retains only the weaker square root bound needed for coefficient 6.01.
-/
theorem principal_log_weight_budget :
    sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) ≤ 6.01 * sqrt (2 * π) := by
  sorry

/-- The first square energy input with convergence proved independently.
Only the numerical budget from page 35 remains OPEN.
-/
theorem principal_log_weight_L2 :
    MemLp principalLogWeight 2 ∧
      sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) ≤ 6.01 * sqrt (2 * π) := by
  exact ⟨LogWeight457.principal_log_weight_memLp_two, principal_log_weight_budget⟩

/-- LEAF. P0014 page 35 display 4.15 and page 43 display 4.42.
The regular numerator has square energy at most two pi times the square of the repaired
Gaussian derivative norm budget. There is no logarithmic derivative in this statement.
-/
theorem gaussian_numerator_L2 (δ : ℝ) :
    MemLp (gaussianNumerator δ) 2 ∧
      sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) ≤
        sqrt (2 * π) * (1 + 6 * |δ|) := by
  exact Numerator457.gaussian_numerator_L2 δ

/-- The principal contour bound from the independent logarithmic and Gaussian energies.
This assembly has no sorry of its own. Only the numerical logarithmic budget remains OPEN.
-/
theorem principal_contour_bound (δ x : ℝ) (hx : 1 ≤ x) :
    ‖principalContour δ x‖ ≤ 6.01 * (1 + 6 * |δ|) / sqrt x := by
  obtain ⟨hL, hLb⟩ := principal_log_weight_L2
  obtain ⟨hG, hGb⟩ := gaussian_numerator_L2 δ
  apply principal_contour_bound_of_L2 δ x hx hL hG
  calc
    _ ≤ (6.01 * sqrt (2 * π)) * (sqrt (2 * π) * (1 + 6 * |δ|)) :=
      mul_le_mul hLb hGb (sqrt_nonneg _) (by positivity)
    _ = (6.01 * (sqrt (2 * π) ^ 2)) * (1 + 6 * |δ|) := by ring
    _ = _ := by rw [sq_sqrt (by positivity : 0 ≤ 2 * π)]; ring

end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.principal_log_weight_L2
#print axioms LeanLab.HelfgottMajor.Decomp457b.principal_log_weight_budget
#print axioms LeanLab.HelfgottMajor.Decomp457b.gaussian_numerator_L2
#print axioms LeanLab.HelfgottMajor.Decomp457b.principal_contour_bound

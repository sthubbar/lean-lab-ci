import LeanLab.ChirreHagen2025.Decomp391a

/-!
Split of `Decomp391a.weighted_explicit_formula`.
Chirre, Hagen and Simonic page 4 equation 3.3 and Remark 7, https://arxiv.org/abs/2206.00819 .
The weighted sum is reached by partial summation from psi, then the explicit formula for psi
is integrated against u to the minus two.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp391aSplitExplicit
open ArithmeticFunction MeasureTheory Set LeanLab.ChirreHagen2025.Decomp391a

/-- LEAF: CHS page 4 equation 3.3, absolute convergence of the zero sum, from the sum of
one over the square of the absolute value of rho over all nontrivial zeros with multiplicity.
Class MEDIUM. -/
theorem zeroTerm_summable (x : ℝ) (hx : 100000 ≤ x) : Summable (zeroTerm x) := by
  sorry

/-- LEAF: CHS page 4, the partial summation step behind equation 3.3:
the sum of Lambda n over n up to x equals psi x over x plus the integral from 1 to x
of psi u over u squared. Class MEDIUM. -/
theorem mangoldt_partial_summation (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Chebyshev.psi x / x + ∫ u in (1 : ℝ)..x, Chebyshev.psi u / u ^ 2 := by
  sorry

/-- LEAF: CHS page 4 equation 3.3 and Remark 7, the integral of the explicit formula for psi
against u to the minus two, with the constant log x minus gamma minus 1, the zero sum and the
elementary tail remainder. Class HARD. -/
theorem psi_integral_explicit (x : ℝ) (hx : 100000 ≤ x) :
    (∫ u in (1 : ℝ)..x, Chebyshev.psi u / u ^ 2) =
      Real.log x - Real.eulerMascheroniConstant - 1 -
        (∑' ρ, zeroTerm x ρ).re + ∫ u in Ioi x, remainderKernel u := by
  sorry

/-- CHS page 4 equation 3.3, exact parent statement.
CONDITIONAL ON the three LEAFs above. -/
theorem weighted_explicit_formula_of_leaves (x : ℝ) (hx : 100000 ≤ x) :
    Summable (zeroTerm x) ∧
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Real.log x - Real.eulerMascheroniConstant + (Chebyshev.psi x - x) / x -
        (∑' ρ, zeroTerm x ρ).re + ∫ u in Ioi x, remainderKernel u := by
  refine ⟨zeroTerm_summable x hx, ?_⟩
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
  rw [mangoldt_partial_summation x hx, psi_integral_explicit x hx]
  have : (Chebyshev.psi x - x) / x = Chebyshev.psi x / x - 1 := by
    field_simp
  rw [this]
  ring

end LeanLab.ChirreHagen2025.Decomp391aSplitExplicit

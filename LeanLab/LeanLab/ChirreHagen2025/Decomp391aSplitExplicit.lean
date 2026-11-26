import LeanLab.ChirreHagen2025.Decomp391a
import LeanLab.ChirreHagen2025.Decomp391aSplitZeroSum

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
theorem zeroTerm_summable (x : ℝ) (hx : 100000 ≤ x) : Summable (zeroTerm x) :=
  Decomp391aSplitZeroSum.zeroTerm_summable_of_leaves x (by linarith)

/-- LEAF: CHS page 4, the partial summation step behind equation 3.3:
the sum of Lambda n over n up to x equals psi x over x plus the integral from 1 to x
of psi u over u squared. Class MEDIUM. -/
theorem mangoldt_partial_summation (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Chebyshev.psi x / x + ∫ u in (1 : ℝ)..x, Chebyshev.psi u / u ^ 2 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hA := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ => (vonMangoldt n : ℝ))
    (f := fun t : ℝ => t⁻¹) (a := 1) (b := x) zero_le_one hx1
    (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      have : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 1 x) := by
        apply ContinuousOn.neg
        apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
        intro t ht; have : (1:ℝ) ≤ t := ht.1; exact pow_ne_zero 2 (lt_of_lt_of_le one_pos this).ne'
      refine (this.integrableOn_Icc).congr_fun (fun t _ => ?_) measurableSet_Icc
      simp [deriv_inv])
  have hL : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      ∑ k ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊, (fun t : ℝ => t⁻¹) (k : ℝ) * (vonMangoldt k : ℝ) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hfl]
    simp [div_eq_inv_mul]
  rw [hL, hA, ← Chebyshev.psi_eq_sum_Icc, intervalIntegral.integral_of_le hx1]
  have h01 : (∑ k ∈ Finset.Icc 0 ⌊(1 : ℝ)⌋₊, (vonMangoldt k : ℝ)) = 0 := by
    simp [Finset.sum_Icc_succ_top]
  rw [h01]
  have hI : (∫ t in Set.Ioc 1 x, deriv (fun t : ℝ => t⁻¹) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt k : ℝ)) =
      -∫ u in Set.Ioc 1 x, Chebyshev.psi u / u ^ 2 := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [deriv_inv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hI]
  simp [div_eq_inv_mul]

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

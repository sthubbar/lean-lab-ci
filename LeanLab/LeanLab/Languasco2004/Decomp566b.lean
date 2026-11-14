/-
Jia 1996 pages 271 to 273, all numerical components for the group 1 remainder.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderIntegral566
import LeanLab.Languasco2004.NumericRest566a
import LeanLab.Languasco2004.NumericRest566b
import LeanLab.Languasco2004.NumericRest566c
import LeanLab.Languasco2004.NumericRest566d
import LeanLab.Languasco2004.NumericRest566e

namespace LeanLab.Languasco2004.Decomp566b
open Real RemainderData566 RemainderKernel566 RemainderIntegral566
noncomputable section

/-- Page 273: the exact polynomial certificates cover all 25 printed coefficients. -/
theorem all_polynomial_lower (i : Fin 25) :
    (coefficient i : ℝ) + 0.00000001 ≤ polynomialTerm i := by
  fin_cases i
  · exact NumericRest566a.block_lower 0
  · exact NumericRest566a.block_lower 1
  · exact NumericRest566a.block_lower 2
  · exact NumericRest566a.block_lower 3
  · exact NumericRest566a.block_lower 4
  · exact NumericRest566b.block_lower 0
  · exact NumericRest566b.block_lower 1
  · exact NumericRest566b.block_lower 2
  · exact NumericRest566b.block_lower 3
  · exact NumericRest566b.block_lower 4
  · exact NumericRest566c.block_lower 0
  · exact NumericRest566c.block_lower 1
  · exact NumericRest566c.block_lower 2
  · exact NumericRest566c.block_lower 3
  · exact NumericRest566c.block_lower 4
  · exact NumericRest566d.block_lower 0
  · exact NumericRest566d.block_lower 1
  · exact NumericRest566d.block_lower 2
  · exact NumericRest566d.block_lower 3
  · exact NumericRest566d.block_lower 4
  · exact NumericRest566e.block_lower 0
  · exact NumericRest566e.block_lower 1
  · exact NumericRest566e.block_lower 2
  · exact NumericRest566e.block_lower 3
  · exact NumericRest566e.block_lower 4

/-- Pages 271 to 273: every exact source integral reaches its coefficient with a reserve. -/
theorem all_term_lower (i : Fin 25) :
    (coefficient i : ℝ) + 0.00000001 ≤ term i :=
  (all_polynomial_lower i).trans (polynomialTerm_le i)

/-- LEAF. Page 273: the full numerical lower model exceeds the printed subtotal. -/
theorem remainder_model_lower : (0.39496525 : ℝ) ≤ model := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => all_term_lower i)
  have hc : (∑ i : Fin 25, (coefficient i : ℝ)) = (0.394965 : ℝ) := by
    norm_num [coefficient, Fin.sum_univ_succ]
  calc (0.39496525 : ℝ) = ∑ i : Fin 25, ((coefficient i : ℝ) + 0.00000001) := by
         rw [Finset.sum_add_distrib, hc]
         norm_num
       _ ≤ ∑ i : Fin 25, term i := h
       _ = model := rfl

/-- Page 273: the model leaves a strict reserve for the prime transfer error. -/
theorem printed_remainder_coefficient_lower : (0.394965 : ℝ) < model := by
  linarith [remainder_model_lower]

#print axioms all_polynomial_lower
#print axioms all_term_lower
#print axioms remainder_model_lower
#print axioms printed_remainder_coefficient_lower
end
end LeanLab.Languasco2004.Decomp566b

/-
Jia 1996 pages 271 to 273, exact polynomial integration for source terms 11 to 15.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderKernel566
import LeanLab.Languasco2004.HornerPiece566_11
import LeanLab.Languasco2004.HornerPiece566_12
import LeanLab.Languasco2004.HornerPiece566_13
import LeanLab.Languasco2004.HornerPiece566_14
import LeanLab.Languasco2004.HornerPiece566_15

namespace LeanLab.Languasco2004.NumericRest566c
open Real intervalIntegral RemainderData566 RemainderKernel566 Numeric548 Numeric30_548
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF. Pages 271 to 273: exact polynomial integration certifies five printed components with reserves. -/
theorem block_lower (j : Fin 5) :
    (coefficient ⟨10 + j.val, by omega⟩ : ℝ) + 0.00000001 ≤
      polynomialTerm ⟨10 + j.val, by omega⟩ := by
  fin_cases j
  · exact HornerPiece566.component_11_polynomial_lower
  · exact HornerPiece566.component_12_polynomial_lower
  · exact HornerPiece566.component_13_polynomial_lower
  · exact HornerPiece566.component_14_polynomial_lower
  · exact HornerPiece566.component_15_polynomial_lower

#print axioms block_lower
end
end LeanLab.Languasco2004.NumericRest566c

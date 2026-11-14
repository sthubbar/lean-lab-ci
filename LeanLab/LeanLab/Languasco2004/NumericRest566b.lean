/-
Jia 1996 pages 271 to 273, exact polynomial integration for source terms 6 to 10.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderKernel566
import LeanLab.Languasco2004.HornerPiece566_06
import LeanLab.Languasco2004.HornerPiece566_07
import LeanLab.Languasco2004.HornerPiece566_08
import LeanLab.Languasco2004.HornerPiece566_09
import LeanLab.Languasco2004.HornerPiece566_10

namespace LeanLab.Languasco2004.NumericRest566b
open Real intervalIntegral RemainderData566 RemainderKernel566 Numeric548 Numeric30_548
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF. Pages 271 to 273: exact polynomial integration certifies five printed components with reserves. -/
theorem block_lower (j : Fin 5) :
    (coefficient ⟨5 + j.val, by omega⟩ : ℝ) + 0.00000001 ≤
      polynomialTerm ⟨5 + j.val, by omega⟩ := by
  fin_cases j
  · exact HornerPiece566.component_06_polynomial_lower
  · exact HornerPiece566.component_07_polynomial_lower
  · exact HornerPiece566.component_08_polynomial_lower
  · exact HornerPiece566.component_09_polynomial_lower
  · exact HornerPiece566.component_10_polynomial_lower

#print axioms block_lower
end
end LeanLab.Languasco2004.NumericRest566b

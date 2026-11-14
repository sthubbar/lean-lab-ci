/-
Jia 1996 pages 271 to 273, exact polynomial integration for source terms 1 to 5.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderKernel566
import LeanLab.Languasco2004.HornerPiece566_01
import LeanLab.Languasco2004.HornerPiece566_02
import LeanLab.Languasco2004.HornerPiece566_03
import LeanLab.Languasco2004.HornerPiece566_04
import LeanLab.Languasco2004.HornerPiece566_05

namespace LeanLab.Languasco2004.NumericRest566a
open Real intervalIntegral RemainderData566 RemainderKernel566 Numeric548 Numeric30_548
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF. Pages 271 to 273: exact polynomial integration certifies five printed components with reserves. -/
theorem block_lower (j : Fin 5) :
    (coefficient ⟨0 + j.val, by omega⟩ : ℝ) + 0.00000001 ≤
      polynomialTerm ⟨0 + j.val, by omega⟩ := by
  fin_cases j
  · exact HornerPiece566.component_01_polynomial_lower
  · exact HornerPiece566.component_02_polynomial_lower
  · exact HornerPiece566.component_03_polynomial_lower
  · exact HornerPiece566.component_04_polynomial_lower
  · exact HornerPiece566.component_05_polynomial_lower

#print axioms block_lower
end
end LeanLab.Languasco2004.NumericRest566a

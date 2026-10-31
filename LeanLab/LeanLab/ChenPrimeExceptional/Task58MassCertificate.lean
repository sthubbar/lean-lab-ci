/-
AI wrote this Lean code for CODEX task58.
One exact rational certificate for the accelerated IB1 quadrature model.
This certificate alone does not identify a real integral.
Binary Goldbach is open.
-/
import Mathlib

open Finset

namespace LeanLab.ChenPrimeExceptional.Task58

/-- The exact integral of the proposed product polynomial. -/
def polynomialMassQ : ℚ :=
  ∑ i ∈ range 60, ∑ j ∈ range 70,
    -(-1 : ℚ) ^ (i + 1) / (i + 1) * (1 + (-1 / 2 : ℚ) ^ j / 2) *
      (7 / 10 : ℚ) ^ (i + j + 2) / (i + j + 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- One kernel checked rational enclosure for the product polynomial mass. -/
theorem polynomialMassQ_bounds :
    (0.49099519 : ℚ) ≤ polynomialMassQ ∧ polynomialMassQ ≤ (0.49099522 : ℚ) := by
  decide +kernel

end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.polynomialMassQ_bounds

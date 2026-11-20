/-
P0069 page 51, E2 before display 5.17.
Concrete hypotheses for the task663 variation quadrature port.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DensitySlope517

namespace LeanLab.BHP1997.Task663
open DecompC165d

/-- The epsilon hypotheses hold and the high branch meets E2. -/
theorem variation_parameters_inhabited :
    ∃ ε a b : ℝ, 0 < ε ∧ ε ≤ 1/10^8 ∧ lowerTwoDiscarded ε a b ∧ 1 ≤ a+3*b := by
  refine ⟨1/200000000, 2/5, 1/4, ?_⟩
  norm_num [lowerTwoDiscarded, upperPairRegion]

/-- The unrestricted trivial character identity fails at modulus two and index zero.
P0069 page 3 condition 1.8 is the character context.
This audits a lab split interface. It is not a paper error claim. -/
theorem principal_trivial_character_statement_false :
    ¬ (∀ q m : ℕ, (1 : DirichletCharacter ℂ q) (m : ZMod q) = 1) := by
  intro h
  have hzero := h 2 0
  have hz : (1 : DirichletCharacter ℂ 2) (0 : ZMod 2) = 0 := MulChar.map_zero _
  rw [Nat.cast_zero, hz] at hzero
  exact zero_ne_one hzero

set_option pp.fullNames true

#print axioms principal_trivial_character_statement_false
#print axioms variation_parameters_inhabited
#print axioms LeanLab.BHP1997.LowerShortC165.leaf_two_variation_quadrature
#print axioms LeanLab.BHP1997.LowerShortC165.two_density_variation

end LeanLab.BHP1997.Task663

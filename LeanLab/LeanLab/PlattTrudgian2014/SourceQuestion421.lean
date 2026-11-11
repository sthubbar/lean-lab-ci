/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 174, the averaged cosine expansion immediately after display 4.11.
This is a QUESTION about the printed extra averaging factor, not a FINDING.
-/
import LeanLab.PlattTrudgian2014.LambdaMoment

namespace LeanLab.PlattTrudgian2014

/-- P0026 page 174, test the printed grid identity on its constant Taylor case.
The coefficient sequence one at zero and zero elsewhere is the exact expansion at t zero.
The printed right side retains a factor one half when the grid has two points. -/
theorem cosine_grid_constant_question421 :
    (∀ x : ℝ, Real.exp ((0 : ℝ) * (G 1 x).re) =
      ∑' k : ℕ, (if k = 0 then (1 : ℝ) else 0) * Real.cos (2 * Real.pi * k * x)) ∧
    ((1 / 2 : ℝ) * (∑ r ∈ Finset.range 2, Real.exp ((0 : ℝ) * (G 1 ((r : ℝ) / 2)).re)) ≠
      (1 / 2 : ℝ) * (∑' k : ℕ,
        (if 2 * k = 0 then (1 : ℝ) else 0) * Real.cos (2 * Real.pi * k * (0 : ℝ)))) := by
  constructor
  · intro x
    simp [ite_mul]
  · norm_num [ite_mul]

set_option format.width 240
#print axioms cosine_grid_constant_question421

end LeanLab.PlattTrudgian2014

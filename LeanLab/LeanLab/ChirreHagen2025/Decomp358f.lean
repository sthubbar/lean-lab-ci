import LeanLab.ChirreHagen2025.Decomp358e
import LeanLab.ChenExplicit.GammaBounds

/-!
P0075 page 5 after equation 2.11, the constant coefficient only.
The positive-index Berndt bounds await a readable source proof.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358f
open Decomp272a

/-- P0075 page 5 equation 2.11, the zeroth coefficient is Euler's constant.
This is an immediate consequence of the existing definitions. -/
theorem laurentCoeff_zero : laurentCoeff 0 = (Real.eulerMascheroniConstant : ℂ) := by
  simp [laurentCoeff, regularPart]

/-- P0075 page 5 last display, the zeroth coefficient has norm below 0.578.
Reuse the lab's proved bound 0.57722 for Euler's constant. -/
theorem laurentCoeff_zero_bound : ‖laurentCoeff 0‖ ≤ (0.578 : ℝ) := by
  rw [laurentCoeff_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
  exact LeanLab.ChenExplicit.Gamma.gamma_lt.le.trans (by norm_num)

end LeanLab.ChirreHagen2025.Decomp358f

import LeanLab.DERZ1997.Decomp1529b
import LeanLab.PNTPort.ZetaZeros.LeftLine

/-!
The unsmoothed left edge for the explicit-formula contour.
Auxiliary bounds for Davenport chapter 17 printed pages 108 and 109.
The constants are derived here from the existing logarithmic derivative bound.
These estimates do not certify the sealed numerical constant 1000.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.DERZ1997.ZetaLeft623
open Complex Real MeasureTheory Set
open LeanLab.Routes.Decomp1551a

example : ∃ C : ℝ, 0 < C ∧ ‖fK 2 (-1 / 2 : ℂ)‖ ≤ C * (2 : ℝ) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := zeta_left_pointwise623
  exact ⟨C, hC, by simpa using hb 2 (by norm_num) 0⟩

example : ∃ C : ℝ, 0 < C ∧
    ‖∫ t in (-2 : ℝ)..2, fK 2 ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * √2 := by
  obtain ⟨C, hC, hb⟩ := zeta_left_integral623
  exact ⟨C, hC, hb 2 2 (by norm_num) (by norm_num) (by norm_num)⟩

end LeanLab.DERZ1997.ZetaLeft623

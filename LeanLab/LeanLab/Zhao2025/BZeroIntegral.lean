import LeanLab.Zhao2025.BZero
import LeanLab.Zhao2025.LaplaceOrder

/-!
Integral form of the zero lambda0 branch.
Source: Zhao 2025, display 2.19, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The two quotients of display 2.19 are elementary Laplace integrals. -/
theorem B_zero_laplace (t l : ℝ) (hl : l ≠ 0) :
    B t l 0 = 1 / 6 * (∫ u in 0..(2 * t), Real.exp (-l * u)) +
      (∫ u in 0..t, Real.exp (-l * u)) ^ 2 := by
  rw [B_zero_eq t l hl,
    exp_integral 0 (2 * t) (-l) (neg_ne_zero.mpr hl),
    exp_integral 0 t (-l) (neg_ne_zero.mpr hl)]
  simp only [mul_zero, Real.exp_zero]
  have h2 : Real.exp (-l * (2 * t)) = Real.exp (-(2 * l * t)) := by congr 1; ring
  have h1 : Real.exp (-l * t) = Real.exp (-(l * t)) := by congr 1; ring
  rw [h2, h1]
  field_simp [hl]
  <;> ring

#print axioms B_zero_laplace

end LeanLab.Zhao2025.Task56

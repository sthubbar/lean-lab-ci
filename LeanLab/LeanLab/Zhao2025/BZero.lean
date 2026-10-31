import LeanLab.Zhao2025.BMonotone

/-!
The lambda0 equals zero branch in the proof of Lemma 2.3.
Source: Zhao 2025, display 2.19, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The zero lambda0 specialization is the printed quotient formula. -/
theorem B_zero_eq (t l : ℝ) (hl : l ≠ 0) :
    B t l 0 = 1 / 6 * ((1 - Real.exp (-(2 * l * t))) / l) +
      ((1 - Real.exp (-(l * t))) / l) ^ 2 := by
  have he : Real.exp (-(2 * l * t)) = Real.exp (-(l * t)) ^ 2 := by
    calc
      _ = Real.exp (-(l * t) + -(l * t)) := by congr 1; ring
      _ = Real.exp (-(l * t)) * Real.exp (-(l * t)) := Real.exp_add _ _
      _ = _ := by ring
  unfold B
  simp only [add_zero, mul_zero, zero_add]
  rw [he]
  field_simp [hl]
  <;> ring

#print axioms B_zero_eq

end LeanLab.Zhao2025.Task56

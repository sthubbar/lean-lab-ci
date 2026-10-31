import Mathlib

/-!
The elementary implication from display 3.25 to display 3.26.
Source: Zhao 2025, displays 3.25 and 3.26, page 11.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56

/-- CONDITIONAL ON display 3.25, with nonnegativity of its excess term explicit. -/
theorem count_from325 (N : ℕ) (D delta e : ℝ) (hD : 0 ≤ D) (hd : 0 ≤ delta)
    (hgap : e < delta ^ 2) (h325 : (delta ^ 2 - e) * (N : ℝ) + 2 * delta * D ≤ 1) :
    (N : ℝ) ≤ 1 / (delta ^ 2 - e) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  nlinarith [mul_nonneg hd hD]

#print axioms count_from325
end LeanLab.Zhao2025.Task56

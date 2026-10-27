import Mathlib

/-!
A quantitative epsilon choice for the two analytic error terms.
Source: Zhao 2025, displays 2.14 and 3.6 to 3.8, pages 5, 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56

/-- Two positive errors can be fixed before the common large modulus threshold. -/
theorem epsilon_budget (e : ℝ) (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ (1 + d) * (1 + d) ≤ 1 + e := by
  let a := min e 1
  have ha : 0 < a := lt_min he (by norm_num)
  have hae : a ≤ e := min_le_left _ _
  have ha1 : a ≤ 1 := min_le_right _ _
  refine ⟨a / 4, by positivity, ?_⟩
  have hs : a ^ 2 ≤ a := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha1)]
  nlinarith

#print axioms epsilon_budget
end LeanLab.Zhao2025.Task56

import LeanLab.Halupczok2012.Statements
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

open scoped BigOperators

namespace LeanLab.Halupczok2012

/-- LEAF: Theorem 6 parameter existence. -/
theorem theorem_6_param_B_exists (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
  ∃ B : ℝ, 0 < B := by
  use 1
  norm_num

/-- LEAF: Theorem 6 parameter C and Y0 existence. -/
theorem theorem_6_param_C_Y0_exists (A ε B c1 c2 c3 : ℝ) (a1 a2 : ℤ) :
  ∃ C Y0 : ℝ, 0 < C ∧ 0 < Y0 := by
  use 1, 1
  exact ⟨by norm_num, by norm_num⟩

/-- LEAF: Abstract statement for Theorem 6 bounds. -/
theorem theorem_6_abstract_bounds (A ε B c1 c2 c3 C Y0 X1 X2 Y Q1 Q2 : ℝ) (a1 a2 : ℤ)
  (hY0 : Y0 ≤ Y) (hc1 : c1 * X1 ^ (2 / 3 + ε) ≤ Y) (hYX1 : Y ≤ X1) (hYX2 : Y ≤ X2)
  (hX2 : X2 ≤ 2 * X1 - Y) (hQ1_1 : 1 ≤ Q1) (hQ1 : Q1 ≤ c2 * Y ^ (3 / 2 : ℝ) * X1 ^ (-(1 / 2) : ℝ))
  (hQ2_1 : 1 ≤ Q2) (hQ2 : Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B)) (ha1 : (a1 : ℝ) ≤ X1) :
  thm6LHS X1 X2 Y Q1 Q2 a1 a2 ≤ C * Y ^ 2 * Real.log Y ^ (-A) := by
  sorry

/-- The assembly theorem for Theorem 6. -/
theorem theorem_6_assembly : Theorem6 := by
  intro A ε hA hε
  obtain ⟨B, hB⟩ := theorem_6_param_B_exists A ε hA hε
  use B, hB
  intro c1 c2 c3 hc1 hc2 hc3 a1 a2
  obtain ⟨C, Y0, hC, hY0⟩ := theorem_6_param_C_Y0_exists A ε B c1 c2 c3 a1 a2
  use C, Y0
  intro X1 X2 Y Q1 Q2 hY0_le hc1_le hY_X1 hY_X2 hX2_le hQ1_1 hQ1_le hQ2_1 hQ2_le ha1_le
  apply theorem_6_abstract_bounds A ε B c1 c2 c3 C Y0 X1 X2 Y Q1 Q2 a1 a2
  · exact hY0_le
  · exact hc1_le
  · exact hY_X1
  · exact hY_X2
  · exact hX2_le
  · exact hQ1_1
  · exact hQ1_le
  · exact hQ2_1
  · exact hQ2_le
  · exact ha1_le

end LeanLab.Halupczok2012

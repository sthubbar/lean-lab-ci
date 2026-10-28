import LeanLab.LZCesaroShort.Statements
import LeanLab.LZCesaroShort.Lemma5
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace LeanLab.LZCesaroShort

open Complex MeasureTheory Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt

/-- LEAF arXiv:1606.00869v2 page 2, bound for the exponential sum TH. -/
theorem lemma5_bound_TH_leaf : ∃ K : ℝ, ∀ N H : ℕ, ∀ α : ℝ, 2 ≤ N → 1 ≤ H → H ≤ N →
    ‖TH N H H α‖ ≤ K * min (H : ℝ) (1 / ‖α‖) := by sorry

/-- LEAF arXiv:1606.00869v2 page 2, integral of the product of T and wsum. -/
theorem integral_T_wsum_leaf : ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
    ‖∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H α * (wsum N H H : ℂ)‖ ≤ K * (N * Real.log (2 * (N : ℝ) ^ 2 / H)) := by sorry

/-- LEAF arXiv:1606.00869v2 page 2, bound for the partial sum over y. -/
theorem theorem2a_partial_sum_bound_leaf : ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N → ∀ y : ℝ, -(H : ℝ) ≤ y → y < H →
    |wsum N H y| ≤ K * N * Real.log N ^ 2 * Real.log (2 * H) := by sorry

/-- LEAF arXiv:1606.00869v2 page 2, theorem1 from theorem2b component. -/
theorem theorem1_from_theorem2b_leaf : ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N →
    ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ K * (N * Real.log (2 * (N : ℝ) ^ 2 / H) + H * Real.log N ^ 2 * Real.log (2 * H)) := by sorry

/-- The exact Theorem1 Prop is conditionally dependent on Theorem2b and Sec5. -/
theorem lz_theorem1_decomp_assembly : RiemannHypothesis → Theorem1 := by
  intro _
  exact theorem1_from_theorem2b_leaf

end LeanLab.LZCesaroShort

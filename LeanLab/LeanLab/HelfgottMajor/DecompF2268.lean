import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_conductor_above_height

/-!
# Split of the tall conductor beyond square estimate, FREE-nv-glm task2268

The target is the upper bound for the book count in the regime `T ≥ 10 ^ 7` and
`T ^ 2 ≤ q`. The analytic content is the upper half of the explicit zero count estimate.
The range is cut once more at `q = T ^ 3`.

On the first side, `q ≤ T ^ 3`, the logarithm of the conductor is controlled by the
logarithm of the height, because `log q ≤ 3 log T`. On the second side, `q > T ^ 3`, the
conductor is the dominant logarithmic parameter. These are proper subranges of the target,
so each analytic leaf is weaker than the target. The third leaf is the identity that expands
the error function.

The assembly uses the two analytic leaves and the error identity. It has no gap of its own.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Upper zero count estimate on the subcase `q ≤ T ^ 3`. The hypotheses are the target
hypotheses together with the conductor scale cut. The conclusion expands the error function, so
it states the analytic upper estimate directly as the count minus the Stirling mean is at most
`0.15 log (qT) + 3.389`. -/
theorem book_zero_count_upper_q_le_T_cubed_expanded_F2268
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT7 : 10 ^ 7 ≤ T) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hq3 : (q : ℝ) ≤ T ^ 3) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ 0.15 * Real.log ((q : ℝ) * T) + 3.389 := by
  sorry

/-- LEAF. Upper zero count estimate on the subcase `q > T ^ 3`. The hypotheses are the target
hypotheses together with the conductor scale cut. The conclusion expands the error function, so
it states the analytic upper estimate directly as the count minus the Stirling mean is at most
`0.15 log (qT) + 3.389`. -/
theorem book_zero_count_upper_q_gt_T_cubed_expanded_F2268
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT7 : 10 ^ 7 ≤ T) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hq3 : T ^ 3 < (q : ℝ)) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ 0.15 * Real.log ((q : ℝ) * T) + 3.389 := by
  sorry

/-- LEAF. Error identity. The book error is exactly `0.15 log (qT) + 3.389`. This algebraic
identity converts the expanded conclusions of the two analytic leaves into the target error. -/
theorem book_error_expansion_F2268 (q : ℕ) (T : ℝ) :
    bookError q T = 0.15 * Real.log ((q : ℝ) * T) + 3.389 := by
  rfl

/-- Assembly of the split. The conductor scale `q = T ^ 3` divides the target range into the
two analytic leaves. The error identity then converts their expanded bound into the target
form. -/
theorem book_zero_count_large_height_upper_tall_conductor_above_height_beyond_squared_tall_F2268
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT7 : 10 ^ 7 ≤ T) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hqs : T ^ 2 ≤ (q : ℝ))
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt (q : ℝ) (T ^ 3) with hq3 | hq3
  · have h := book_zero_count_upper_q_le_T_cubed_expanded_F2268
      χ hχ hT hT7 hq hTq hq3 hmain
    rw [book_error_expansion_F2268]
    exact h
  · have h := book_zero_count_upper_q_gt_T_cubed_expanded_F2268
      χ hχ hT hT7 hq hTq hq3 hmain
    rw [book_error_expansion_F2268]
    exact h

end LeanLab.HelfgottMajor.ZeroCount1623

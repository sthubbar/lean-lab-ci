/-
P0042 page 432, the ratio constant on a subrange of its published interval.
This reuses the existing kernel minGB bound through 1e9. It extends no Goldbach computation.
The full ratio conclusion remains CONDITIONAL only on the full maximum bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.RatioReductionTask72
import LeanLab.Verifications.Top50.MinGB1e9

namespace LeanLab.Verifications.RatioKernelTask72

open CitedInputs RatioReductionTask72

/-- A proved alias for the existing kernel bound, with no input hypothesis. -/
theorem small_prefix_kernel :
    ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 10 ^ 9 → minGB n ≤ 1789 :=
  Top50.Bits.minGB_le_1789_upTo_1e9

/-- The P0042 ratio bound on even n from 300000000 through 1e9, with no cited input. -/
theorem ratio_middle_kernel :
    ∀ n : ℕ, Even n → 300000000 ≤ n → n ≤ 10 ^ 9 →
      (minGB n : ℝ) < 1.603 * Real.log n ^ 2 * Real.log (Real.log n) :=
  ratio_middle_of_small

/-- CONDITIONAL only on the full maximum bound. Both prefixes are kernel proved. -/
theorem ratio_of_max_and_low (hmax : P0042MinimalBound) :
    P0042RatioBound :=
  ratio_of_max_and_prefixes hmax

end LeanLab.Verifications.RatioKernelTask72

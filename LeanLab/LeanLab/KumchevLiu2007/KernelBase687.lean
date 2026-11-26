/-
Kumchev and Liu 2007, P0088, page 7 before display 27.
Shared kernel declarations moved unchanged from KernelSumSplit1122.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc

namespace LeanLab.KumchevLiu2007.KernelSumSplit1122

open Real LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.Prep1121KLMajor
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The kernel K_b of the display before 27: 1 - 2b at k = 0, -sin(2 pi k b)/(pi k) else. -/
noncomputable def Kb (b : ℝ) (k : ℤ) : ℝ :=
  (if k = 0 then 1 else 0) -
    (if k = 0 then 2 * b else Real.sin (2 * π * (k : ℝ) * b) / (π * (k : ℝ)))

/-- The scale b = P^3/(q Y) of the leaf, written as in its statement. -/
noncomputable def bq (X ε : ℝ) (B : ℝ) (q : ℕ) : ℝ :=
  (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q

/-- The inner sum over the integer window with weight 1/log m1. -/
noncomputable def innerSum (X Y b : ℝ) (n m2 : ℕ) : ℝ :=
  ∑ m1 ∈ primeWindow X Y, 1 / Real.log (m1 : ℝ) * Kb b (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ))

/-- Decay away from the two window edges: min of 1 and 1/(b (d + 1)), d the distance of
n - m2^2 to the edges X - Y and X. -/
noncomputable def edgeDecay (X Y b : ℝ) (n m2 : ℕ) : ℝ :=
  min 1 (1 / (b * (min |(n : ℝ) - (m2 : ℝ) ^ 2 - (X - Y)| |(n : ℝ) - (m2 : ℝ) ^ 2 - X| + 1)))

/-- PROVED. Swap of the two sums and the triangle inequality. -/
theorem kernel_sum_swap (X Y z b : ℝ) (n : ℕ) :
    |∑ m1 ∈ primeWindow X Y, ∑ m2 ∈ squareWindow Y,
        1 / Real.log (m1 : ℝ) * f2Weight z (m2 : ℝ) *
          Kb b (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ))| ≤
      ∑ m2 ∈ squareWindow Y, |f2Weight z (m2 : ℝ)| * |innerSum X Y b n m2| := by
  rw [Finset.sum_comm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun m2 _ => ?_))
  rw [← abs_mul, innerSum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m1 _ => ?_
  ring

end LeanLab.KumchevLiu2007.KernelSumSplit1122

/-
P0088 page 7 before display 27. The unchanged kernel tail statement is proved here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelInner687
import LeanLab.KumchevLiu2007.KernelEdge687

namespace LeanLab.KumchevLiu2007.Burst1122B27
open Real LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.Prep1121KLMajor
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- P0088 page 7 before display 27. The original finite kernel tail estimate, proved
from the finite primitive, logarithmic weight variation and square spacing. -/
theorem kernel_sum_bound :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B → ∀ n : ℕ,
        |∑ m1 ∈ primeWindow X (windowY X ε), ∑ m2 ∈ squareWindow (windowY X ε),
          1 / Real.log (m1 : ℝ) *
            f2Weight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m2 : ℝ) *
          ((if -(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) = 0 then 1 else 0) -
            (if -(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) = 0 then
              2 * ((windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q) else
              Real.sin (2 * π * ((-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) *
                  ((windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ) / Real.log X ^ B)⁻¹ / q)) /
                (π * ((-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) : ℤ) : ℝ))))| ≤
          C * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-2 : ℤ) := by
  intro B hB ε hε hε'
  obtain ⟨C, X1, hC, hI⟩ := KernelSumSplit1122.inner_window_bound B hB ε hε hε'
  obtain ⟨C', X2, hC', hO⟩ := KernelSumSplit1122.outer_square_bound B hB ε hε hε' C hC
  refine ⟨C', max X1 X2, hC', fun X hX q hq1 hqP n => ?_⟩
  have h1 : X1 ≤ X := (le_max_left _ _).trans hX
  have h2 : X2 ≤ X := (le_max_right _ _).trans hX
  let Y := windowY X ε
  let z := Y ^ (1/4:ℝ) * (Real.log X ^ B) ^ (-2:ℤ)
  let b := KernelSumSplit1122.bq X ε B q
  change |∑ m1 ∈ primeWindow X Y, ∑ m2 ∈ squareWindow Y,
    1 / Real.log (m1:ℝ) * f2Weight z (m2:ℝ) *
      KernelSumSplit1122.Kb b (-(n:ℤ)+(m1:ℤ)+((m2^2:ℕ):ℤ))| ≤ _
  apply (KernelSumSplit1122.kernel_sum_swap X Y z b n).trans
  apply (Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
    (hI X h1 q hq1 hqP n m hm) (abs_nonneg (f2Weight z (m:ℝ)))).trans
  exact hO X h2 q hq1 hqP n

end LeanLab.KumchevLiu2007.Burst1122B27

#print axioms LeanLab.KumchevLiu2007.Burst1122B27.kernel_sum_bound

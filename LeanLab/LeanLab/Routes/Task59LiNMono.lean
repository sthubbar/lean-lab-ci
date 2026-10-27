/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
Monotonicity of the discrete logarithmic integral used by U1436.
-/
import LeanLab.PNTPort.BVMax.Primes

namespace LeanLab.Routes.Task59

open Finset Real LeanLab.PNTPort.BVMax

/-- The discrete logarithmic integral increases with its natural argument. -/
theorem liN_mono : Monotone liN := by
  intro m n hmn
  unfold liN
  apply sum_le_sum_of_subset_of_nonneg
  · exact Icc_subset_Icc le_rfl hmn
  · intro k hk _
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
    exact div_nonneg (by norm_num) (log_nonneg hk1)

example : liN 2 ≤ liN 3 := liN_mono (by decide)

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.liN_mono

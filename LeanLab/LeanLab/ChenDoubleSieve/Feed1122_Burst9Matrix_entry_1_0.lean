import LeanLab.ChenDoubleSieve.Table1Algebra
import LeanLab.ChenDoubleSieve.KernelIntegrability

/-!
# Feed 1122 split of `Burst9Matrix.entry_1_0`

Source: Wu 2004, arXiv 0705.1652, display 7.1, kernel Xi2 of display 3.22, page 15; matrix `A` on page 31.
The parent asks that the truncated Maple value `1537386/10^7` be a lower bound for
`a_{2,1} = ∫ tableKernel 1` over the grid panel `[1, 11/5]`. The split cuts the panel at
its midpoint `8/5` by additivity of the interval integral. The two half panel bounds were computed
in double precision Gauss Legendre quadrature with breakpoints at every window endpoint,
whole panel value 0.153738679505, margin 7.950e-08, shared between the halves.
This file does not import `Burst9Matrix`, to avoid a cycle.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_1_0

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15: the kernel of row 2 is interval integrable on the panel
`[1, 11/5]`; it is a finite sum of window indicators times continuous functions and the
continuous term `σ₀(t)`. MEDIUM. -/
theorem leaf_integrable :
    IntervalIntegrable (tableKernel 1) volume (1 : ℝ) (11/5 : ℝ) := by
  exact (Burst8P2.table_kernel_integrable 1).mono_set
    (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, left half panel `[1, 8/5]` of `a_{2,1}`:
quadrature value 0.020524429244, stated bound leaves 3.98e-08. HARD. -/
theorem leaf_left :
    (20524389491/1000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(8/5 : ℝ), tableKernel 1 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, right half panel `[8/5, 11/5]` of `a_{2,1}`:
quadrature value 0.133214250261, stated bound leaves 3.98e-08. HARD. -/
theorem leaf_right :
    (133214210511/1000000000000 : ℝ) ≤ ∫ t in (8/5 : ℝ)..(11/5 : ℝ), tableKernel 1 t := by
  sorry

/-- `Burst9Matrix.entry_1_0` from the three leaves: additivity of the integral at `8/5`. -/
theorem entry_1_0_of_leaves : (candidateMatrixQ 1 0 : ℝ) ≤ integralMatrix 1 0 := by
  have hc : (candidateMatrixQ 1 0 : ℝ) = (768693/5000000 : ℝ) := by
    norm_num [candidateMatrixQ]
  have he : integralMatrix 1 0 = ∫ t in (1 : ℝ)..(11/5 : ℝ), tableKernel 1 t := by
    simp only [integralMatrix, Wu04Functional.grid]
    norm_num
  have hI := leaf_integrable
  have h1 : IntervalIntegrable (tableKernel 1) volume (1 : ℝ) (8/5 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))
  have h2 : IntervalIntegrable (tableKernel 1) volume (8/5 : ℝ) (11/5 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; norm_num) Set.right_mem_uIcc)
  rw [hc, he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hl := leaf_left
  have hr := leaf_right
  have hn : (768693/5000000 : ℝ) ≤ (20524389491/1000000000000 : ℝ) + (133214210511/1000000000000 : ℝ) := by norm_num
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_1_0

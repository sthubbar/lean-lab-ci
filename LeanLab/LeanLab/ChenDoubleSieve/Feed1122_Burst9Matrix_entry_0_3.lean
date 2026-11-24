import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Feed 1122 split of `Burst9Matrix.entry_0_3`

Source: Wu 2004, arXiv 0705.1652, display 7.1, kernel Xi2 of display 3.22, page 15; matrix `A` on page 31.
The parent asks that the truncated Maple value `269346/10^7` be a lower bound for
`a_{1,4} = ∫ tableKernel 0` over the grid panel `[12/5, 5/2]`. The split cuts the panel at
its midpoint `49/20` by additivity of the interval integral. The two half panel bounds were computed
in double precision Gauss Legendre quadrature with breakpoints at every window endpoint,
whole panel value 0.026934690635, margin 9.063e-08, shared between the halves.
This file does not import `Burst9Matrix`, to avoid a cycle.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_0_3

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15: the kernel of row 1 is interval integrable on the panel
`[12/5, 5/2]`; it is a finite sum of window indicators times continuous functions and the
continuous term `σ₀(t)`. MEDIUM. -/
theorem leaf_integrable :
    IntervalIntegrable (tableKernel 0) volume (12/5 : ℝ) (5/2 : ℝ) := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, left half panel `[12/5, 49/20]` of `a_{1,4}`:
quadrature value 0.013443554130, stated bound leaves 4.53e-08. MEDIUM. -/
theorem leaf_left :
    (3360877203/250000000000 : ℝ) ≤ ∫ t in (12/5 : ℝ)..(49/20 : ℝ), tableKernel 0 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, right half panel `[49/20, 5/2]` of `a_{1,4}`:
quadrature value 0.013491136505, stated bound leaves 4.53e-08. MEDIUM. -/
theorem leaf_right :
    (13491091189/1000000000000 : ℝ) ≤ ∫ t in (49/20 : ℝ)..(5/2 : ℝ), tableKernel 0 t := by
  sorry

/-- `Burst9Matrix.entry_0_3` from the three leaves: additivity of the integral at `49/20`. -/
theorem entry_0_3_of_leaves : (candidateMatrixQ 0 3 : ℝ) ≤ integralMatrix 0 3 := by
  have hc : (candidateMatrixQ 0 3 : ℝ) = (134673/5000000 : ℝ) := by
    norm_num [candidateMatrixQ]
  have he : integralMatrix 0 3 = ∫ t in (12/5 : ℝ)..(5/2 : ℝ), tableKernel 0 t := by
    simp only [integralMatrix, Wu04Functional.grid]
    norm_num
  have hI := leaf_integrable
  have h1 : IntervalIntegrable (tableKernel 0) volume (12/5 : ℝ) (49/20 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))
  have h2 : IntervalIntegrable (tableKernel 0) volume (49/20 : ℝ) (5/2 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; norm_num) Set.right_mem_uIcc)
  rw [hc, he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hl := leaf_left
  have hr := leaf_right
  have hn : (134673/5000000 : ℝ) ≤ (3360877203/250000000000 : ℝ) + (13491091189/1000000000000 : ℝ) := by norm_num
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_0_3

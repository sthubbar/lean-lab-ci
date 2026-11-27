import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Feed 1122 split of `Burst9Matrix.entry_3_0`

Source: Wu 2004, arXiv 0705.1652, display 7.1, kernel Xi2 of display 3.22, page 15; matrix `A` on page 31.
The parent asks that the truncated Maple value `1549103/10^7` be a lower bound for
`a_{4,1} = ∫ tableKernel 3` over the grid panel `[1, 11/5]`. The split cuts the panel at
its midpoint `8/5` by additivity of the interval integral. The two half panel bounds were computed
in double precision Gauss Legendre quadrature with breakpoints at every window endpoint,
whole panel value 0.154910347391, margin 4.739e-08, shared between the halves.
This file does not import `Burst9Matrix`, to avoid a cycle.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_3_0

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15: the kernel of row 4 is interval integrable on the panel
`[1, 11/5]`; it is a finite sum of window indicators times continuous functions and the
continuous term `σ₀(t)`. MEDIUM. -/
theorem leaf_integrable :
    IntervalIntegrable (tableKernel 3) volume (1 : ℝ) (11/5 : ℝ) := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, left half panel `[1, 8/5]` of `a_{4,1}`:
quadrature value 0.028980830855, stated bound leaves 2.37e-08. HARD. -/
theorem leaf_left :
    (28980807159/1000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(8/5 : ℝ), tableKernel 3 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, right half panel `[8/5, 11/5]` of `a_{4,1}`:
quadrature value 0.125929516536, stated bound leaves 2.37e-08. HARD. -/
theorem leaf_right :
    (62964746421/500000000000 : ℝ) ≤ ∫ t in (8/5 : ℝ)..(11/5 : ℝ), tableKernel 3 t := by
  sorry

/-- `Burst9Matrix.entry_3_0` from the three leaves: additivity of the integral at `8/5`. -/
theorem entry_3_0_of_leaves : (candidateMatrixQ 3 0 : ℝ) ≤ integralMatrix 3 0 := by
  have hc : (candidateMatrixQ 3 0 : ℝ) = (1549103/10000000 : ℝ) := by
    norm_num [candidateMatrixQ]
  have he : integralMatrix 3 0 = ∫ t in (1 : ℝ)..(11/5 : ℝ), tableKernel 3 t := by
    simp only [integralMatrix, Wu04Functional.grid]
    norm_num
  have hI := leaf_integrable
  have h1 : IntervalIntegrable (tableKernel 3) volume (1 : ℝ) (8/5 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))
  have h2 : IntervalIntegrable (tableKernel 3) volume (8/5 : ℝ) (11/5 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; norm_num) Set.right_mem_uIcc)
  rw [hc, he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hl := leaf_left
  have hr := leaf_right
  have hn : (1549103/10000000 : ℝ) ≤ (28980807159/1000000000000 : ℝ) + (62964746421/500000000000 : ℝ) := by norm_num
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_3_0

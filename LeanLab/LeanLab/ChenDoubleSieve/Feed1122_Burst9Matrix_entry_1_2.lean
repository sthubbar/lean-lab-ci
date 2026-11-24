import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Feed 1122 split of `Burst9Matrix.entry_1_2`

Source: Wu 2004, arXiv 0705.1652, display 7.1, kernel Xi2 of display 3.22, page 15; matrix `A` on page 31.
The parent asks that the truncated Maple value `260352/10^7` be a lower bound for
`a_{2,3} = ∫ tableKernel 1` over the grid panel `[23/10, 12/5]`. The split cuts the panel at
its midpoint `47/20` by additivity of the interval integral. The two half panel bounds were computed
in double precision Gauss Legendre quadrature with breakpoints at every window endpoint,
whole panel value 0.026035202309, margin 2.309e-09, shared between the halves.
This file does not import `Burst9Matrix`, to avoid a cycle.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_1_2

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15: the kernel of row 2 is interval integrable on the panel
`[23/10, 12/5]`; it is a finite sum of window indicators times continuous functions and the
continuous term `σ₀(t)`. MEDIUM. -/
theorem leaf_integrable :
    IntervalIntegrable (tableKernel 1) volume (23/10 : ℝ) (12/5 : ℝ) := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, left half panel `[23/10, 47/20]` of `a_{2,3}`:
quadrature value 0.012973480643, stated bound leaves 1.16e-09. MEDIUM. -/
theorem leaf_left :
    (12973479487/1000000000000 : ℝ) ≤ ∫ t in (23/10 : ℝ)..(47/20 : ℝ), tableKernel 1 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, right half panel `[47/20, 12/5]` of `a_{2,3}`:
quadrature value 0.013061721667, stated bound leaves 1.15e-09. MEDIUM. -/
theorem leaf_right :
    (6530860257/500000000000 : ℝ) ≤ ∫ t in (47/20 : ℝ)..(12/5 : ℝ), tableKernel 1 t := by
  sorry

/-- `Burst9Matrix.entry_1_2` from the three leaves: additivity of the integral at `47/20`. -/
theorem entry_1_2_of_leaves : (candidateMatrixQ 1 2 : ℝ) ≤ integralMatrix 1 2 := by
  have hc : (candidateMatrixQ 1 2 : ℝ) = (2034/78125 : ℝ) := by
    norm_num [candidateMatrixQ]
  have he : integralMatrix 1 2 = ∫ t in (23/10 : ℝ)..(12/5 : ℝ), tableKernel 1 t := by
    simp only [integralMatrix, Wu04Functional.grid]
    norm_num
  have hI := leaf_integrable
  have h1 : IntervalIntegrable (tableKernel 1) volume (23/10 : ℝ) (47/20 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))
  have h2 : IntervalIntegrable (tableKernel 1) volume (47/20 : ℝ) (12/5 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; norm_num) Set.right_mem_uIcc)
  rw [hc, he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hl := leaf_left
  have hr := leaf_right
  have hn : (2034/78125 : ℝ) ≤ (12973479487/1000000000000 : ℝ) + (6530860257/500000000000 : ℝ) := by norm_num
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_1_2

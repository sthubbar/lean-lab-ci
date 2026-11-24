import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Feed 1122 split of `Burst9Matrix.entry_1_1`

Source: Wu 2004, arXiv 0705.1652, display 7.1, kernel Xi2 of display 3.22, page 15; matrix `A` on page 31.
The parent asks that the truncated Maple value `255908/10^7` be a lower bound for
`a_{2,2} = ∫ tableKernel 1` over the grid panel `[11/5, 23/10]`. The split cuts the panel at
its midpoint `9/4` by additivity of the interval integral. The two half panel bounds were computed
in double precision Gauss Legendre quadrature with breakpoints at every window endpoint,
whole panel value 0.025590860759, margin 6.076e-08, shared between the halves.
This file does not import `Burst9Matrix`, to avoid a cycle.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_1_1

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15: the kernel of row 2 is interval integrable on the panel
`[11/5, 23/10]`; it is a finite sum of window indicators times continuous functions and the
continuous term `σ₀(t)`. MEDIUM. -/
theorem leaf_integrable :
    IntervalIntegrable (tableKernel 1) volume (11/5 : ℝ) (23/10 : ℝ) := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, left half panel `[11/5, 9/4]` of `a_{2,2}`:
quadrature value 0.012728618695, stated bound leaves 3.04e-08. MEDIUM. -/
theorem leaf_left :
    (2545717663/200000000000 : ℝ) ≤ ∫ t in (11/5 : ℝ)..(9/4 : ℝ), tableKernel 1 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, right half panel `[9/4, 23/10]` of `a_{2,2}`:
quadrature value 0.012862242064, stated bound leaves 3.04e-08. MEDIUM. -/
theorem leaf_right :
    (6431105843/500000000000 : ℝ) ≤ ∫ t in (9/4 : ℝ)..(23/10 : ℝ), tableKernel 1 t := by
  sorry

/-- `Burst9Matrix.entry_1_1` from the three leaves: additivity of the integral at `9/4`. -/
theorem entry_1_1_of_leaves : (candidateMatrixQ 1 1 : ℝ) ≤ integralMatrix 1 1 := by
  have hc : (candidateMatrixQ 1 1 : ℝ) = (63977/2500000 : ℝ) := by
    norm_num [candidateMatrixQ]
  have he : integralMatrix 1 1 = ∫ t in (11/5 : ℝ)..(23/10 : ℝ), tableKernel 1 t := by
    simp only [integralMatrix, Wu04Functional.grid]
    norm_num
  have hI := leaf_integrable
  have h1 : IntervalIntegrable (tableKernel 1) volume (11/5 : ℝ) (9/4 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))
  have h2 : IntervalIntegrable (tableKernel 1) volume (9/4 : ℝ) (23/10 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; norm_num) Set.right_mem_uIcc)
  rw [hc, he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hl := leaf_left
  have hr := leaf_right
  have hn : (63977/2500000 : ℝ) ≤ (2545717663/200000000000 : ℝ) + (6431105843/500000000000 : ℝ) := by norm_num
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_1_1

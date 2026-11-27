import LeanLab.ChenDoubleSieve.Table1Algebra
import LeanLab.ChenDoubleSieve.Burst8P2

/-!
# Feed 1122 split of `Burst9Matrix.entry_0_4`

Source: Wu 2004, arXiv 0705.1652, display 7.1, kernel Xi2 of display 3.22, page 15; matrix `A` on page 31.
The parent asks that the truncated Maple value `271084/10^7` be a lower bound for
`a_{1,5} = ∫ tableKernel 0` over the grid panel `[5/2, 13/5]`. The split cuts the panel at
its midpoint `51/20` by additivity of the interval integral. The two half panel bounds were computed
in double precision Gauss Legendre quadrature with breakpoints at every window endpoint,
whole panel value 0.027108478244, margin 7.824e-08, shared between the halves.
This file does not import `Burst9Matrix`, to avoid a cycle.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_0_4

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15: the kernel of row 1 is interval integrable on the panel
`[5/2, 13/5]`; it is a finite sum of window indicators times continuous functions and the
continuous term `σ₀(t)`. MEDIUM. -/
theorem leaf_integrable :
    IntervalIntegrable (tableKernel 0) volume (5/2 : ℝ) (13/5 : ℝ) := by
  have h₁ : IntervalIntegrable (tableKernel 0) volume (1 : ℝ) (3 : ℝ) := by
    -- Use the general integrability result for table kernels on [1, 3]
    have h₂ : ∀ i : Fin 9, IntervalIntegrable (Wu04Table.tableKernel i) volume (1 : ℝ) (3 : ℝ) := by
      apply LeanLab.ChenDoubleSieve.Burst8P2.table_kernel_integrable
    -- Specialize to i = 0 (the first row)
    have h₃ : IntervalIntegrable (Wu04Table.tableKernel (0 : Fin 9)) volume (1 : ℝ) (3 : ℝ) := h₂ (0 : Fin 9)
    simpa [Wu04Table.tableKernel] using h₃
  -- Restrict the interval from [1, 3] to [5/2, 13/5]
  have h₂ : IntervalIntegrable (tableKernel 0) volume (5/2 : ℝ) (13/5 : ℝ) := by
    have h₃ : IntervalIntegrable (tableKernel 0) volume (5/2 : ℝ) (13/5 : ℝ) := h₁.mono_set (Set.uIcc_subset_uIcc (by norm_num) (by norm_num))
    exact h₃
  exact h₂

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, left half panel `[5/2, 51/20]` of `a_{1,5}`:
quadrature value 0.013516138048, stated bound leaves 3.91e-08. MEDIUM. -/
theorem leaf_left :
    (540643957/40000000000 : ℝ) ≤ ∫ t in (5/2 : ℝ)..(51/20 : ℝ), tableKernel 0 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, right half panel `[51/20, 13/5]` of `a_{1,5}`:
quadrature value 0.013592340196, stated bound leaves 3.91e-08. MEDIUM. -/
theorem leaf_right :
    (13592301077/1000000000000 : ℝ) ≤ ∫ t in (51/20 : ℝ)..(13/5 : ℝ), tableKernel 0 t := by
  sorry

/-- `Burst9Matrix.entry_0_4` from the three leaves: additivity of the integral at `51/20`. -/
theorem entry_0_4_of_leaves : (candidateMatrixQ 0 4 : ℝ) ≤ integralMatrix 0 4 := by
  have hc : (candidateMatrixQ 0 4 : ℝ) = (67771/2500000 : ℝ) := by
    norm_num [candidateMatrixQ]
  have he : integralMatrix 0 4 = ∫ t in (5/2 : ℝ)..(13/5 : ℝ), tableKernel 0 t := by
    simp only [integralMatrix, Wu04Functional.grid]
    norm_num
  have hI := leaf_integrable
  have h1 : IntervalIntegrable (tableKernel 0) volume (5/2 : ℝ) (51/20 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))
  have h2 : IntervalIntegrable (tableKernel 0) volume (51/20 : ℝ) (13/5 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; norm_num) Set.right_mem_uIcc)
  rw [hc, he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hl := leaf_left
  have hr := leaf_right
  have hn : (67771/2500000 : ℝ) ≤ (540643957/40000000000 : ℝ) + (13592301077/1000000000000 : ℝ) := by norm_num
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_0_4

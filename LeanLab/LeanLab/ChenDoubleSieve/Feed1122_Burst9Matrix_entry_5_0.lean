import LeanLab.ChenDoubleSieve.Table1Algebra
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_left
import LeanLab.ChenDoubleSieve.KernelIntegrability

/-!
# Feed 1122 split of `Burst9Matrix.entry_5_0`

Source: Wu 2004, arXiv 0705.1652, display 7.2, kernel Xi1 of display 3.21, page 14; matrix `A` on page 31.
The parent asks that the truncated Maple value `1602317/10^7` be a lower bound for
`a_{6,1} = ∫ tableKernel 5` over the grid panel `[1, 11/5]`. The split cuts the panel at
its midpoint `8/5` by additivity of the interval integral. The two half panel bounds were computed
in double precision Gauss Legendre quadrature with breakpoints at every window endpoint,
whole panel value 0.160231748826, margin 4.883e-08, shared between the halves.
This file does not import `Burst9Matrix`, to avoid a cycle.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.2, kernel Xi1 of display 3.21, page 14: the kernel of row 6 is interval integrable on the panel
`[1, 11/5]`; it is a finite sum of window indicators times continuous functions and the
continuous term `σ₀(t)`. MEDIUM. -/
theorem leaf_integrable :
    IntervalIntegrable (tableKernel 5) volume (1 : ℝ) (11/5 : ℝ) := by
  have hI : IntervalIntegrable (tableKernel 5) volume (1 : ℝ) (3 : ℝ) := by
    -- `tableKernel 5 = Ξ₁(27/10, 347/100)` with `(27/10, 347/100)` admissible, so `Ξ₁` is
    -- interval-integrable on `[1, 3]` by the existing kernel-integrability lemma.
    exact LeanLab.ChenDoubleSieve.Burst8P2.table_kernel_integrable 5
  -- Restrict the interval from `[1, 3]` to `[1, 11/5]`.
  exact hI.mono_set (by
    intro t ht
    have h₁ : (1 : ℝ) ≤ t := ht.1
    have h₂ : t ≤ 11 / 5 := ht.2
    have h₃ : (11 / 5 : ℝ) ≤ (3 : ℝ) := by norm_num
    have h₄ : t ≤ (3 : ℝ) := by linarith
    exact ⟨by norm_num, by linarith⟩
  end)

/-- LEAF: Wu 2004 display 7.2, kernel Xi1 of display 3.21, page 14, left half panel `[1, 8/5]` of `a_{6,1}`:
quadrature value 0.039796938721, stated bound leaves 2.44e-08. HARD. -/
theorem leaf_left :
    (9949228577/250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(8/5 : ℝ), tableKernel 5 t :=
  Feed1122_Burst9Matrix_entry_5_0_p2_left.left_half_of_leaves

/-- LEAF: Wu 2004 display 7.2, kernel Xi1 of display 3.21, page 14, right half panel `[8/5, 11/5]` of `a_{6,1}`:
quadrature value 0.120434810104, stated bound leaves 2.44e-08. HARD. -/
theorem leaf_right :
    (120434785693/1000000000000 : ℝ) ≤ ∫ t in (8/5 : ℝ)..(11/5 : ℝ), tableKernel 5 t :=
  Feed1122_Burst9Matrix_entry_5_0_p2_right.right_half

/-- `Burst9Matrix.entry_5_0` from the three leaves: additivity of the integral at `8/5`. -/
theorem entry_5_0_of_leaves : (candidateMatrixQ 5 0 : ℝ) ≤ integralMatrix 5 0 := by
  have hc : (candidateMatrixQ 5 0 : ℝ) = (1602317/10000000 : ℝ) := by
    norm_num [candidateMatrixQ]
  have he : integralMatrix 5 0 = ∫ t in (1 : ℝ)..(11/5 : ℝ), tableKernel 5 t := by
    simp only [integralMatrix, Wu04Functional.grid]
    norm_num
  have hI := leaf_integrable
  have h1 : IntervalIntegrable (tableKernel 5) volume (1 : ℝ) (8/5 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))
  have h2 : IntervalIntegrable (tableKernel 5) volume (8/5 : ℝ) (11/5 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; norm_num) Set.right_mem_uIcc)
  rw [hc, he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hl := leaf_left
  have hr := leaf_right
  have hn : (1602317/10000000 : ℝ) ≤ (9949228577/250000000000 : ℝ) + (120434785693/1000000000000 : ℝ) := by norm_num
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0

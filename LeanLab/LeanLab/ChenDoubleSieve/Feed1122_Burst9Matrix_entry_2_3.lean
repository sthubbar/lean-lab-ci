import LeanLab.ChenDoubleSieve.Table1Algebra
import LeanLab.ChenDoubleSieve.KernelIntegrability

/-!
# Feed 1122 split of `Burst9Matrix.entry_2_3`

Source: Wu 2004, arXiv 0705.1652, display 7.1, kernel Xi2 of display 3.22, page 15; matrix `A` on page 31.
The parent asks that the truncated Maple value `257327/10^7` be a lower bound for
`a_{3,4} = ∫ tableKernel 2` over the grid panel `[12/5, 5/2]`. The split cuts the panel at
its midpoint `49/20` by additivity of the interval integral. The two half panel bounds were computed
in double precision Gauss Legendre quadrature with breakpoints at every window endpoint,
whole panel value 0.025732778853, margin 7.885e-08, shared between the halves.
This file does not import `Burst9Matrix`, to avoid a cycle.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_2_3

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15: the kernel of row 3 is interval integrable on the panel
`[12/5, 5/2]`; it is a finite sum of window indicators times continuous functions and the
continuous term `σ₀(t)`. MEDIUM. -/
theorem leaf_integrable :
    IntervalIntegrable (tableKernel 2) volume (12/5 : ℝ) (5/2 : ℝ) := by
  have h₁ : IntervalIntegrable (tableKernel 2) volume (1 : ℝ) (3 : ℝ) := by
    have h₂ : tableKernel 2 = Wu04Functional.Xi2 (Wu04Functional.tableParams ⟨2, by decide⟩) := by
      dsimp [Wu04Table.tableKernel]
      <;> rfl
    rw [h₂]
    -- Use the general Xi2_integrable lemma from KernelIntegrability
    have h₃ : (3 : ℝ) < (Wu04Functional.tableParams ⟨2, by decide⟩).sp := by norm_num [Wu04Functional.tableParams, Wu04Functional.Params]
    have h₄ : ∀ t ∈ Set.Icc (1 : ℝ) (3 : ℝ),
        let a := Wu04Functional.alpha (Wu04Functional.tableParams ⟨2, by decide⟩)
        let P := ((Wu04Functional.tableParams ⟨2, by decide⟩).s - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).sp - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k1 - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k2 - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k3 - 1)
        ((a 1 ≤ t ∧ t ≤ 3) → 0 < P ∧ P ≤ (t + 1) ^ 5) ∧
        ((a 8 ≤ t ∧ t ≤ a 0) → 0 < ((Wu04Functional.tableParams ⟨2, by decide⟩).k2 - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k1 - 1 - t) ∧ ((Wu04Functional.tableParams ⟨2, by decide⟩).k2 - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k1 - 1 - t) ≤ t + 1) ∧
        ((a 4 ≤ t ∧ t ≤ a 1) → 0 < ((Wu04Functional.tableParams ⟨2, by decide⟩).k3 - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).sp - 1 - t) ∧ ((Wu04Functional.tableParams ⟨2, by decide⟩).k3 - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).sp - 1 - t) ≤ t + 1) ∧
        ((a 2 ≤ t ∧ t ≤ a 1) → 0 < ((Wu04Functional.tableParams ⟨2, by decide⟩).s - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).sp - 1 - t) ∧ ((Wu04Functional.tableParams ⟨2, by decide⟩).s - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).sp - 1 - t) ≤ t + 1) ∧
        ((a 0 ≤ t ∧ t ≤ a 1) → 0 < ((Wu04Functional.tableParams ⟨2, by decide⟩).k1 - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k2 - 1) ∧ ((Wu04Functional.tableParams ⟨2, by decide⟩).k1 - 1) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k2 - 1) ≤ (t + 1) ^ 2) ∧
        ((a 6 ≤ t ∧ t ≤ a 4) → 0 < ((Wu04Functional.tableParams ⟨2, by decide⟩).k1 * (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).k1 * t) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k3 * (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).k3 * t) ∧ ((Wu04Functional.tableParams ⟨2, by decide⟩).k1 * (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).k1 * t) * ((Wu04Functional.tableParams ⟨2, by decide⟩).k3 * (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).k3 * t) ≤ (Wu04Functional.tableParams ⟨2, by decide⟩).sp ^ 2) ∧
        ((a 4 ≤ t ∧ t ≤ a 7) → 0 < (Wu04Functional.tableParams ⟨2, by decide⟩).k1 * (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).k1 * t ∧ (Wu04Functional.tableParams ⟨2, by decide⟩).k1 * (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).k1 * t ≤ (Wu04Functional.tableParams ⟨2, by decide⟩).sp * ((Wu04Functional.tableParams ⟨2, by decide⟩).sp - 1 - t)) ∧
        ((a 5 ≤ t ∧ t ≤ a 7) → 0 < (Wu04Functional.tableParams ⟨2, by decide⟩).k2 * (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).k2 * t ∧ (Wu04Functional.tableParams ⟨2, by decide⟩).k2 * (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).sp - (Wu04Functional.tableParams ⟨2, by decide⟩).k2 * t ≤ (Wu04Functional.tableParams ⟨2, by decide⟩).sp) ∧
        ((a 7 ≤ t ∧ t ≤ a 1) → 0 < (1 : ℝ) ∧ 1 ≤ (Wu04Functional.tableParams ⟨2, by decide⟩).sp - 1 - t) := by
      intro t ht
      have h₅ := LeanLab.ChenDoubleSieve.Burst8P2.tableParams_Xi2Signs ⟨2, by decide⟩ t ht
      simpa [Wu04Functional.alpha, Wu04Functional.tableParams, Wu04Functional.Params] using h₅
    -- Apply Xi2_integrable
    have h₅ : IntervalIntegrable (Wu04Functional.Xi2 (Wu04Functional.tableParams ⟨2, by decide⟩)) volume (1 : ℝ) (3 : ℝ) :=
      LeanLab.ChenDoubleSieve.Burst8P2.Xi2_integrable h₃ h₄
    exact h₅
  -- Restrict the interval from [1, 3] to [12/5, 5/2]
  have h₂ : IntervalIntegrable (tableKernel 2) volume (12/5 : ℝ) (5/2 : ℝ) := by
    have h₃ : IntervalIntegrable (tableKernel 2) volume (12/5 : ℝ) (5/2 : ℝ) :=
      h₁.mono_set (Set.uIcc_subset_uIcc (by norm_num [Set.mem_uIcc]) (by norm_num [Set.mem_uIcc]))
    exact h₃
  exact h₂

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, left half panel `[12/5, 49/20]` of `a_{3,4}`:
quadrature value 0.012834022807, stated bound leaves 3.94e-08. MEDIUM. -/
theorem leaf_left :
    (12833983379/1000000000000 : ℝ) ≤ ∫ t in (12/5 : ℝ)..(49/20 : ℝ), tableKernel 2 t := by
  sorry

/-- LEAF: Wu 2004 display 7.1, kernel Xi2 of display 3.22, page 15, right half panel `[49/20, 5/2]` of `a_{3,4}`:
quadrature value 0.012898756047, stated bound leaves 3.94e-08. MEDIUM. -/
theorem leaf_right :
    (6449358311/500000000000 : ℝ) ≤ ∫ t in (49/20 : ℝ)..(5/2 : ℝ), tableKernel 2 t := by
  sorry

/-- `Burst9Matrix.entry_2_3` from the three leaves: additivity of the integral at `49/20`. -/
theorem entry_2_3_of_leaves : (candidateMatrixQ 2 3 : ℝ) ≤ integralMatrix 2 3 := by
  have hc : (candidateMatrixQ 2 3 : ℝ) = (257327/10000000 : ℝ) := by
    norm_num [candidateMatrixQ]
  have he : integralMatrix 2 3 = ∫ t in (12/5 : ℝ)..(5/2 : ℝ), tableKernel 2 t := by
    simp only [integralMatrix, Wu04Functional.grid]
    norm_num
  have hI := leaf_integrable
  have h1 : IntervalIntegrable (tableKernel 2) volume (12/5 : ℝ) (49/20 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.mem_uIcc]; norm_num))
  have h2 : IntervalIntegrable (tableKernel 2) volume (49/20 : ℝ) (5/2 : ℝ) :=
    hI.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; norm_num) Set.right_mem_uIcc)
  rw [hc, he, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hl := leaf_left
  have hr := leaf_right
  have hn : (257327/10000000 : ℝ) ≤ (12833983379/1000000000000 : ℝ) + (6449358311/500000000000 : ℝ) := by norm_num
  linarith

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_2_3
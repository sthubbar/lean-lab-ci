import LeanLab.ChenDoubleSieve.Table1Algebra

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
  have h₁ : IntervalIntegrable (tableKernel 2) volume (12/5 : ℝ) (5/2 : ℝ) := by
    -- tableKernel 2 = Xi2 (tableParams 2) since 2 < 4
    have h₂ : (tableKernel 2 : ℝ → ℝ) = (fun t : ℝ => Wu04Functional.Xi2 (Wu04Functional.tableParams (⟨2, by decide⟩ : Fin 4)) t) := by
      funext t
      simp [Wu04Table.tableKernel]
      <;> rfl
    rw [h₂]
    -- Prove that Xi2 is interval integrable by showing it's a sum of interval integrable functions
    -- Each term in Xi2 is of the form (indicator * continuous) or sigma0 * constant
    -- We use the fact that continuous functions on compact intervals are interval integrable
    -- and indicator functions are piecewise constant with finitely many pieces
    -- The product of a piecewise constant function and a continuous function is piecewise continuous
    -- with finitely many pieces, hence interval integrable
    have h₃ : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi2 (Wu04Functional.tableParams (⟨2, by decide⟩ : Fin 4)) t) volume (12/5 : ℝ) (5/2 : ℝ) := by
      -- Use the general fact that a bounded measurable function on a compact interval is interval integrable
      -- In Lean, we can use the connection between IntervalIntegrable and MeasureTheory.IntegrableOn
      have h₄ : MeasureTheory.IntegrableOn (fun t : ℝ => Wu04Functional.Xi2 (Wu04Functional.tableParams (⟨2, by decide⟩ : Fin 4)) t) (Set.Icc (12/5 : ℝ) (5/2 : ℝ)) volume := by
        -- The function is a sum of terms, each of which is bounded and measurable
        -- We can prove each term is integrable and then use the fact that the sum of integrable functions is integrable
        -- For now, we use a more direct approach: the function is continuous almost everywhere and bounded
        -- This is a standard result in measure theory
        -- We use the fact that the function is piecewise continuous with finitely many discontinuities
        -- and hence Riemann integrable, which implies Lebesgue integrable
        have h₅ : ContinuousOn (fun t : ℝ => Wu04Functional.Xi2 (Wu04Functional.tableParams (⟨2, by decide⟩ : Fin 4)) t) (Set.Icc (12/5 : ℝ) (5/2 : ℝ) \ { (123/50 : ℝ) }) := by
          -- Prove continuity on the interval minus the discontinuity point
          -- The only discontinuity in [12/5, 5/2] is at a1 = 2.46 = 123/50
          -- On the two subintervals [12/5, 123/50] and [123/50, 5/2], the function is continuous
          sorry
        -- A continuous function on a compact set minus a finite set is bounded and measurable
        -- and hence integrable
        have h₆ : MeasureTheory.IntegrableOn (fun t : ℝ => Wu04Functional.Xi2 (Wu04Functional.tableParams (⟨2, by decide⟩ : Fin 4)) t) (Set.Icc (12/5 : ℝ) (5/2 : ℝ)) volume := by
          sorry
        exact h₆
      -- Convert MeasureTheory.IntegrableOn to IntervalIntegrable
      have h₇ : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi2 (Wu04Functional.tableParams (⟨2, by decide⟩ : Fin 4)) t) volume (12/5 : ℝ) (5/2 : ℝ) := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (12/5 : ℝ) ≤ (5/2 : ℝ))]
        exact h₄
      exact h₇
    exact h₃
  exact h₁

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

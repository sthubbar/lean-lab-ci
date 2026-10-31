import LeanLab.Zhao2025.UniformMargin

/-!
The uniform gap of display 1.10 for the finite case layouts.
The small case is CONDITIONAL ON SmallCaseZeroEstimates for displays 4.1, 4.3 and 4.4.
All later cases retain the old wrapper bounds. Display 4.5 is derived.
The layout labels specify which S entries are heads and which are R plus T.
Source: Zhao 2025, display 1.10, page 3, and Section 4, pages 13 to 16.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6900

/-- The gap depends only on the lower bound for the first zero. -/
noncomputable def gap (c0 : ℝ) : ℝ := min (4 * c0) 0.001

/-- CONDITIONAL ON the repaired CaseInputs, with the small analytic input named. -/
theorem uniform_energy (c0 : ℝ) (hc0 : 0 < c0) (k : Fin 11) (n : ℕ)
    (l11 : ℝ) (R T S : ℕ → ℝ) (hlower : c0 ≤ l11)
    (h : CaseInputs k n l11 R T S) :
    0 < gap c0 ∧ layoutEnergy k n R T S ≤ 1 - gap c0 := by
  have hg : 0 < gap c0 := lt_min (by linarith) (by norm_num)
  refine ⟨hg, ?_⟩
  by_cases hlow : 0.01 ≤ l11
  · have hb := non_small_bound k n l11 R T S h hlow
    have hm := min_le_right (4 * c0) (0.001 : ℝ)
    unfold gap
    linarith
  · have hk : k = 0 := by
      fin_cases k <;> simp only [CaseInputs] at h
      · rfl
      all_goals exfalso; apply hlow; linarith [h.1]
    subst k
    obtain ⟨hl, hu, hsmall⟩ := h
    have hs := small_case_square_bound n l11 S hl hu hsmall
    have hcut := small_case_cutoff_spec l11 hl
    have hb := case1_bound l11 (smallCaseCutoff l11) hl hu hcut.2.1 hcut.2.2
    have hm := min_le_left (4 * c0) (0.001 : ℝ)
    change ∑ i ∈ Finset.range (n + 1), S i ^ 2 ≤ 1 - gap c0
    unfold gap
    linarith

#print axioms uniform_energy

end LeanLab.Zhao2025.Task56

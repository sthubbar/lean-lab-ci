/-
F-0010. P0085 Alsetri 2025, arXiv 2505.09648 v2 and v3, Lemma 2.2, Case 4: the printed chain
9 + (99 − 31W)/2 + m²W − W ≤ 49.5 + W(m² − 16.5) < 3m² drops the 9. The left side equals
58.5 + W(m² − 16.5), which exceeds 49.5 + W(m² − 16.5) by 9 and reaches 3m² + 9 at W = 3.
The lemma's target (2.5), U + V − W ≤ 3m² + 9, survives: `half_lemma22_core` proves it.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.DensityGoldbach

theorem alsetri_lemma22_case4_expand (m W : ℝ) :
    9 + (99 - 31 * W) / 2 + m ^ 2 * W - W = 58.5 + W * (m ^ 2 - 16.5) := by ring

/-- The printed middle step is false for every `m, W`: the left side is 9 more. -/
theorem alsetri_lemma22_case4_printed_false (m W : ℝ) :
    ¬ (9 + (99 - 31 * W) / 2 + m ^ 2 * W - W ≤ 49.5 + W * (m ^ 2 - 16.5)) := by
  rw [alsetri_lemma22_case4_expand]; norm_num

/-- At `W = 3` the corrected bound is exactly `3m² + 9`, so the printed `< 3m²` fails too. -/
theorem alsetri_lemma22_case4_at3 (m : ℝ) :
    9 + (99 - 31 * 3) / 2 + m ^ 2 * 3 - 3 = 3 * m ^ 2 + 9 := by ring

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.alsetri_lemma22_case4_printed_false

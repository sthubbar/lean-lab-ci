import Mathlib

/-!
# Helfgott's book, Part IV of 2020-04-01, Proposition 16.19: the arithmetic of its constants

Unit U-6456, CLOUD 20261020T1318Z-cloud43, P0014. AI wrote this file.

Source: book pages 444 and 445, copy papers/P0014-book-PartIV.pdf. Write `L = log(qT/2π)`; the
hypotheses `T ≥ max(2πe²/q, 40)` give `L ≥ 2` and `T ≥ 40`.

* `step_545`, `step_1422`, `step_392`: `0.538L + 0.48/T ≤ 0.545L`, `1.409L + 0.96/T ≤ 1.422L`,
  `0.387L + 0.353/T ≤ 0.392L`;
* `mh_norm`: `(1/2π) · 11.99871 ≤ 1.90966`, from (A.35);
* `products`: `1.90966 · 0.545 ≤ 1.041`, `1.90966 · 1.422 ≤ 2.716`, `1.90966 · 0.392 ≤ 0.749`,
  then rounded up to the `1.05`, `2.72`, `0.75` of (16.60).

All MATCH. Ternary Goldbach is a theorem; binary Goldbach is OPEN. AI-written Lean code, Claude,
2026-10-20.
-/

namespace LeanLab.HelfgottMajor.BookP1619

theorem step_545 {L T : ℝ} (hL : 2 ≤ L) (hT : 40 ≤ T) : 0.538 * L + 0.48 / T ≤ 0.545 * L := by
  have : 0.48 / T ≤ 0.012 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

theorem step_1422 {L T : ℝ} (hL : 2 ≤ L) (hT : 40 ≤ T) : 1.409 * L + 0.96 / T ≤ 1.422 * L := by
  have : 0.96 / T ≤ 0.024 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

theorem step_392 {L T : ℝ} (hL : 2 ≤ L) (hT : 40 ≤ T) : 0.387 * L + 0.353 / T ≤ 0.392 * L := by
  have : 0.353 / T ≤ 0.008825 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

theorem mh_norm : 11.99871 / (2 * Real.pi) ≤ 1.90966 := by
  have := Real.pi_gt_d6
  rw [div_le_iff₀ (by positivity)]; linarith

theorem products : (1.90966 : ℝ) * 0.545 ≤ 1.041 ∧ (1.90966 : ℝ) * 1.422 ≤ 2.716 ∧
    (1.90966 : ℝ) * 0.392 ≤ 0.749 ∧ (1.041 : ℝ) ≤ 1.05 ∧ (2.716 : ℝ) ≤ 2.72 ∧ (0.749 : ℝ) ≤ 0.75 := by
  norm_num

end LeanLab.HelfgottMajor.BookP1619

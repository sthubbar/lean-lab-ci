/-
An interior witness for the approximation selection question at P0013 page 70.
This does not refute any analytic leaf. It tests the parameter inference alone.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Approximation325

namespace LeanLab.HelfgottArcs.Decomp119

/-- Both approximations are valid while the reset misses the page 70 alternatives strictly.
Source: P0013 pages 3 and 70, a derived witness for the selection premise question. -/
theorem reset_strict_interior_counterexample325 :
    MinorHyp 2.16e20 (1 / 54000000000000 - 1 / (2 * 2.16e20 * 10000000))
      1 27000000000000 (-1 / 10000000) ∧
      (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6 < (27000000000000 : ℝ) ∧
      2 * (1 / 54000000000000 - 1 / (2 * 2.16e20 * 10000000) : ℝ) =
        0 / 1 + (8000000 - 1 / 10000000) / 2.16e20 ∧
      (1 : ℝ) ≤ (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) ∧
      |(8000000 - 1 / 10000000 : ℝ) / 2.16e20| ≤
        1 / ((1 : ℝ) * ((2.16e20 : ℝ) ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))) ∧
      (1 : ℝ) < (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6 ∧
      |(8000000 - 1 / 10000000 : ℝ) * 1| <
        8 * ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6) := by
  have h1 := MinorQAMGM.x0_cbrt
  have h2 : (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) = (6e6 : ℝ) ^ (2 : ℕ) := by
    calc
      _ = ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        norm_num
      _ = _ := by rw [h1]
  have hs2 : (2 : ℝ) < Real.sqrt 6 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs3 : Real.sqrt (6 : ℝ) ≤ 3 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · norm_num [MinorHyp, h2]
  · rw [h1]; norm_num
  · rw [h2, le_div_iff₀ (by positivity)]
    norm_num
    linarith
  · rw [h2, one_mul, one_div_div]
    norm_num
    linarith
  · rw [h1]; norm_num
  · rw [h1]; norm_num

example := reset_strict_interior_counterexample325

end LeanLab.HelfgottArcs.Decomp119

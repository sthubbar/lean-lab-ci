/-
P0093 pages 164 and 165 equations 7.15 through 7.19.
The small entropy parameter choice in the written binary count argument.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Linnik1951

/-- P0093 pages 164 and 165 equations 7.15 through 7.19. Choose a
positive exceptional fraction below one half with arbitrarily small
binomial entropy exponent. This is independent of the binary phase set. -/
theorem entropy_fraction439 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      ε * Real.log (Real.exp 1 / ε) ≤ δ * Real.log 2 := by
  have hc : ContinuousAt (fun x : ℝ => x - x * Real.log x) 0 :=
    continuous_id.continuousAt.sub Real.continuous_mul_log.continuousAt
  have ht : 0 < δ * Real.log 2 := mul_pos hδ (Real.log_pos (by norm_num))
  obtain ⟨ρ, hρ, hb⟩ := Metric.continuousAt_iff.mp hc _ ht
  let ε := min (ρ / 2) (1 / 4 : ℝ)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hερ : ε < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεhalf : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨ε, hε, hεhalf, ?_⟩
  have hdist : dist ε 0 < ρ := by simpa [Real.dist_eq, abs_of_pos hε] using hερ
  have hsmall := hb hdist
  simp only [Real.dist_eq, zero_mul, sub_zero] at hsmall
  have hle : ε - ε * Real.log ε ≤ δ * Real.log 2 := (le_abs_self _).trans hsmall.le
  rw [Real.log_div (Real.exp_pos 1).ne' hε.ne', Real.log_exp]
  nlinarith

end LeanLab.Linnik1951

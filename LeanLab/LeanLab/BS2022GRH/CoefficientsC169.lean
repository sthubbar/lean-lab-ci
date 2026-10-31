/- AI wrote this Lean code for CODEX task169.
Journal Lemmas 12 and 13, pp. 1229 to 1231. Goldbach is open. -/
import LeanLab.BS2022GRH.EndpointC169
import LeanLab.BS2022GRH.QG

namespace LeanLab.BS2022GRH.CoefficientsC169
open Real ChenThresholdGRH

/-- The journal coefficient pG is at most 0.402 on its printed range, p. 1229. -/
theorem pGJ_le (X : ℝ) (hX : 4e18 ≤ X) : pGJ X ≤ 0.402 := by
  unfold pGJ
  linarith [qG_le_all X hX]

/-- The journal coefficient cG is at most 0.402 on its printed range, p. 1230. -/
theorem cGJ_le (X : ℝ) (hX : 4e18 ≤ X) : cGJ X ≤ 0.402 := by
  have hX0 : 0 < X := by linarith
  have hq := qG_le_all X hX
  have hs : (2e9 : ℝ) ≤ sqrt X := by
    rw [← sqrtX]
    exact sqrt_le_sqrt hX
  have hL : 42.83 ≤ log X := logX_bounds.1.trans (log_le_log (by norm_num) hX)
  have hll : (1 : ℝ) ≤ log (log X) := by
    apply (le_log_iff_exp_le (by linarith)).mpr
    linarith [exp_one_lt_d9]
  have htail : 0.85 / (sqrt X * log (log X)) ≤ 0.85 / (2e9 * 1) := by gcongr
  unfold cGJ pGJ
  linarith

/-- Both journal coefficients lie in the printed nonnegative range, pp. 1229 and 1230. -/
theorem coefficient_ranges (X : ℝ) (hX : 4e18 ≤ X) :
    0 ≤ pGJ X ∧ pGJ X ≤ 0.402 ∧ 0 ≤ cGJ X ∧ cGJ X ≤ 0.402 := by
  have hX0 : 0 < X := by linarith
  have hL : 2 ≤ log X := by
    have := logX_bounds.1.trans (log_le_log (by norm_num) hX)
    linarith
  have hq := EndpointC169.qG_nonneg X hX0 hL
  refine ⟨?_, pGJ_le X hX, EndpointC169.cGJ_nonneg X hX0 hL, cGJ_le X hX⟩
  unfold pGJ
  positivity

/-- Increasing the threshold decreases pG, the endpoint replacement in Lemma 12. -/
theorem pGJ_antitone (X Y : ℝ) (hX : 4e18 ≤ X) (hXY : X ≤ Y) : pGJ Y ≤ pGJ X := by
  have hq := DecompC164a.qG_antitone X Y (by linarith) hXY
  unfold pGJ
  linarith

/-- Increasing the threshold decreases cG, the endpoint replacement in Lemma 13. -/
theorem cGJ_antitone (X Y : ℝ) (hX : 4e18 ≤ X) (hXY : X ≤ Y) : cGJ Y ≤ cGJ X := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le hX0 hXY
  have hL : 42.83 ≤ log X := logX_bounds.1.trans (log_le_log (by norm_num) hX)
  have hLX : 0 < log X := by linarith
  have hll : 0 < log (log X) := log_pos (by linarith)
  have hlog := log_le_log hX0 hXY
  have hllXY := log_le_log hLX hlog
  have htail : 0.85 / (sqrt Y * log (log Y)) ≤ 0.85 / (sqrt X * log (log X)) := by
    gcongr
  unfold cGJ
  exact add_le_add (pGJ_antitone X Y hX hXY) htail

end LeanLab.BS2022GRH.CoefficientsC169

#print axioms LeanLab.BS2022GRH.CoefficientsC169.pGJ_le
#print axioms LeanLab.BS2022GRH.CoefficientsC169.cGJ_le
#print axioms LeanLab.BS2022GRH.CoefficientsC169.coefficient_ranges
#print axioms LeanLab.BS2022GRH.CoefficientsC169.pGJ_antitone
#print axioms LeanLab.BS2022GRH.CoefficientsC169.cGJ_antitone

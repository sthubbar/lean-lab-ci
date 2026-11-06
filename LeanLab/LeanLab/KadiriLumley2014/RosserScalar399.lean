/-
P0059 page 7 displays 2.40 to 2.42 and source 4, arXiv 1310.6374 page 8 Corollary 2.6.
Elementary positivity and monotonicity of q with the published Rosser constants.
AI wrote this Lean code. CODEX task399. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LeanLab.KadiriLumley2014.Task399

open Real Set
open Task259

/-- All three real factors in the denominator of q are positive above T0. -/
theorem countQ_domain {T : ℝ} (hT : 1132491 ≤ T) :
    0 < T ∧ 0 < Real.log T ∧ 0 < Real.log (T / (2 * π)) := by
  have hT0 : 0 < T := by linarith
  have hpi : 0 < 2 * π := by positivity
  have hp : 2 * π < T := by linarith [Real.pi_lt_four]
  exact ⟨hT0, Real.log_pos (by linarith), Real.log_pos ((one_lt_div hpi).mpr hp)⟩

/-- The Rosser q correction is positive on the whole published ordinate domain. -/
theorem countQ_pos {T : ℝ} (hT : 1132491 ≤ T) : 0 < countQ T := by
  obtain ⟨h0, hlog, hshift⟩ := countQ_domain hT
  unfold countQ
  positivity

/-- Cancelling the positive log T gives a decreasing numerator for q. -/
theorem countQ_factor {T : ℝ} (hT : 1132491 ≤ T) :
    countQ T = (0.137 + 0.443 / Real.log T) / (T * Real.log (T / (2 * π))) := by
  obtain ⟨h0, hlog, hshift⟩ := countQ_domain hT
  unfold countQ
  field_simp

/-- q decreases from T0 onward. The proof uses a decreasing positive numerator
and an increasing positive denominator rather than a derivative estimate. -/
theorem countQ_antitone {T U : ℝ} (hT : 1132491 ≤ T) (hTU : T ≤ U) :
    countQ U ≤ countQ T := by
  obtain ⟨hT0, hLT, hST⟩ := countQ_domain hT
  obtain ⟨hU0, hLU, hSU⟩ := countQ_domain (hT.trans hTU)
  have hlog : Real.log T ≤ Real.log U := Real.log_le_log hT0 hTU
  have hlogShift : Real.log (T / (2 * π)) ≤ Real.log (U / (2 * π)) :=
    Real.log_le_log (div_pos hT0 (by positivity)) (div_le_div_of_nonneg_right hTU (by positivity))
  have hnum : (0.137 : ℝ) + 0.443 / Real.log U ≤ 0.137 + 0.443 / Real.log T := by
    gcongr
  have hden : T * Real.log (T / (2 * π)) ≤ U * Real.log (U / (2 * π)) :=
    mul_le_mul hTU hlogShift hST.le hU0.le
  rw [countQ_factor hT, countQ_factor (hT.trans hTU)]
  exact div_le_div₀ (by positivity) hnum (mul_pos hT0 hST) hden

/-- The Rosser remainder is positive from T0 onward, including both logarithm terms. -/
theorem countRemainder_pos {T : ℝ} (hT : 1132491 ≤ T) : 0 < countRemainder T := by
  have hT0 : 0 < T := by linarith
  have he : Real.exp 1 < T := Real.exp_one_lt_three.trans_le (by linarith)
  have hlog : 1 < Real.log T := (Real.lt_log_iff_exp_lt hT0).mpr he
  have hloglog : 0 < Real.log (Real.log T) := Real.log_pos hlog
  unfold countRemainder
  positivity

end LeanLab.KadiriLumley2014.Task399

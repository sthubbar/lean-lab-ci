/-
The logarithmic weight norm in Helfgott equation A.17.
Source: https://arxiv.org/abs/1205.5252v4, page 77.
AI wrote this Lean code for CODEX task62. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.WeightBounds

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real

/-- The elementary antiderivative used for the logarithmic weight norm. -/
theorem integral_log_sq_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, Real.log t ^ 2) =
      b * (Real.log b ^ 2 - 2 * Real.log b + 2) -
        a * (Real.log a ^ 2 - 2 * Real.log a + 2) := by
  have hpos : ∀ t ∈ uIcc a b, 0 < t := fun t ht =>
    lt_of_lt_of_le (lt_min ha hb) ht.1
  have hc : ContinuousOn (fun t : ℝ => Real.log t) (uIcc a b) :=
    continuousOn_id.log (fun t ht => (hpos t ht).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => t * Real.log t ^ 2 - 2 * t * Real.log t + 2 * t)]
  · ring
  · intro t ht
    have hl := Real.hasDerivAt_log (hpos t ht).ne'
    have hd := (((hasDerivAt_id' t).mul (hl.pow 2)).sub
      (((hasDerivAt_id' t).const_mul 2).mul hl)).add
      ((hasDerivAt_id' t).const_mul 2)
    exact hd.congr_deriv (by simp only [Pi.pow_apply]; field_simp [(hpos t ht).ne']; ring)
  · exact (hc.pow 2).intervalIntegrable

/-- Equation A.17, the L1 norm of log times eta2. -/
theorem integral_abs_log_eta2 : (∫ t, |Real.log t * eta2 t|) = 2 - Real.log 4 := by
  have hL : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hR : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hc : ContinuousOn (fun t : ℝ => |Real.log t * eta2 t|) (Ioi 0) :=
    ((continuousOn_id.log (fun t ht => ne_of_gt ht)).mul eta2_continuous.continuousOn).abs
  have hcL : ContinuousOn (fun t : ℝ => Real.log (4 * t)) (Icc (1 / 4) (1 / 2)) := by
    apply (continuousOn_const.mul continuousOn_id).log
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact mul_ne_zero (by norm_num) ht0.ne'
  have iLogL : IntervalIntegrable (fun t => Real.log (4 * t)) volume (1 / 4) (1 / 2) :=
    hcL.intervalIntegrable_of_Icc hL
  have iSqL : IntervalIntegrable (fun t => Real.log (4 * t) ^ 2) volume (1 / 4) (1 / 2) :=
    (hcL.pow 2).intervalIntegrable_of_Icc hL
  have iaL : IntervalIntegrable (fun t => |Real.log t * eta2 t|) volume (1 / 4) (1 / 2) :=
    (hc.mono (fun t ht => show 0 < t from by linarith [ht.1])).intervalIntegrable_of_Icc hL
  have iaR : IntervalIntegrable (fun t => |Real.log t * eta2 t|) volume (1 / 2) 1 :=
    (hc.mono (fun t ht => show 0 < t from by linarith [ht.1])).intervalIntegrable_of_Icc hR
  have eL : (∫ t in (1 / 4 : ℝ)..(1 / 2), |Real.log t * eta2 t|) =
      4 * Real.log 4 * (∫ t in (1 / 4 : ℝ)..(1 / 2), Real.log (4 * t)) -
        4 * (∫ t in (1 / 4 : ℝ)..(1 / 2), Real.log (4 * t) ^ 2) := by
    rw [intervalIntegral.integral_congr (g := fun t =>
      4 * Real.log 4 * Real.log (4 * t) - 4 * Real.log (4 * t) ^ 2)]
    · rw [intervalIntegral.integral_sub (iLogL.const_mul _) (iSqL.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · intro t ht
      rw [uIcc_of_le hL] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hn : Real.log t ≤ 0 := Real.log_nonpos ht0.le (by linarith [ht.2])
      dsimp only
      rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hn (eta2_nonneg t)),
        eta2_of_mem_left ht.1 ht.2, Real.log_mul (by norm_num) ht0.ne']
      ring
  have eR : (∫ t in (1 / 2 : ℝ)..1, |Real.log t * eta2 t|) =
      4 * (∫ t in (1 / 2 : ℝ)..1, Real.log t ^ 2) := by
    rw [intervalIntegral.integral_congr (g := fun t => 4 * Real.log t ^ 2),
      intervalIntegral.integral_const_mul]
    intro t ht
    rw [uIcc_of_le hR] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hn : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
    dsimp only
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hn (eta2_nonneg t)),
      eta2_of_mem_right ht.1 ht.2]
    ring
  have jL1 : (∫ t in (1 / 4 : ℝ)..(1 / 2), Real.log (4 * t)) =
      (2 * Real.log 2 - 1) / 4 := by
    rw [intervalIntegral.integral_comp_mul_left (fun t => Real.log t)
      (by norm_num : (4 : ℝ) ≠ 0), integral_log]
    norm_num
    ring
  have jL2 : (∫ t in (1 / 4 : ℝ)..(1 / 2), Real.log (4 * t) ^ 2) =
      (2 * Real.log 2 ^ 2 - 4 * Real.log 2 + 2) / 4 := by
    rw [intervalIntegral.integral_comp_mul_left (fun t => Real.log t ^ 2)
      (by norm_num : (4 : ℝ) ≠ 0), integral_log_sq_pos _ _ (by norm_num) (by norm_num)]
    norm_num
    ring
  have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  have jR2 : (∫ t in (1 / 2 : ℝ)..1, Real.log t ^ 2) =
      (4 - 2 * Real.log 2 ^ 2 - 4 * Real.log 2) / 4 := by
    rw [integral_log_sq_pos _ _ (by norm_num) (by norm_num), hh]
    norm_num
    ring
  have hwhole : (∫ t, |Real.log t * eta2 t|) =
      ∫ t in (1 / 4 : ℝ)..1, |Real.log t * eta2 t| := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (1 / 4 : ℝ) 1)]
    · rw [← intervalIntegral.integral_of_le (hL.trans hR)]
    · intro t ht
      have hz : eta2 t = 0 := by
        apply le_antisymm _ (eta2_nonneg t)
        apply le_of_not_gt
        intro hp
        have hs := (eta2_pos_iff t).1 hp
        exact ht ⟨hs.1, hs.2.le⟩
      rw [hz, mul_zero, abs_zero]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals iaL iaR,
    eL, eR, jL1, jL2, jR2, h4]
  ring

end LeanLab.HelfgottArcs

/-
The first derivative L1 identity behind Helfgott equation 2.6 and Lemma A.3.
Source: https://arxiv.org/abs/1205.5252v4, pages 7 and 75.
AI wrote this Lean code for CODEX task62. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Eta2TV
import LeanLab.HelfgottArcs.WeightBounds

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real Filter Topology

/-- The integral of the absolute value of the actual derivative is twice the peak value. -/
theorem integral_abs_deriv_eta2rho {ρ : ℝ} (hρ : 4 ≤ ρ) :
    (∫ t, |deriv (eta2rho ρ) t|) = 2 * eta2rho ρ (1 / 2) := by
  have hr : 0 < ρ := by linarith
  have hL : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hR : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have signL : ∀ t ∈ Icc (1 / 4 : ℝ) (1 / 2), 0 ≤ gL ρ t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hm := mul_le_mul_of_nonneg_right hρ (sq_nonneg t)
    have hq : 1 ≤ 4 * ρ * t ^ 2 := by nlinarith [ht.1, sq_nonneg (t - 1 / 4)]
    exact mul_nonneg (by norm_num) (div_nonneg (Real.log_nonneg hq) ht0.le)
  have signR : ∀ t ∈ Icc (1 / 2 : ℝ) 1, gR ρ t ≤ 0 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hm := mul_le_mul_of_nonneg_right hρ (sq_nonneg t)
    have hq : 1 ≤ ρ * t ^ 2 := by nlinarith [ht.1, sq_nonneg (t - 1 / 2)]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (div_nonneg (Real.log_nonneg hq) ht0.le)
  have eqL : EqOn (fun t => |deriv (eta2rho ρ) t|) (gL ρ)
      (Ioo (1 / 4 : ℝ) (1 / 2)) := by
    intro t ht
    dsimp only
    rw [(eta2rho_hasDerivAt_left hr ht.1 ht.2).deriv]
    exact abs_of_nonneg (signL t ⟨ht.1.le, ht.2.le⟩)
  have eqR : EqOn (fun t => |deriv (eta2rho ρ) t|) (fun t => -gR ρ t)
      (Ioo (1 / 2 : ℝ) 1) := by
    intro t ht
    dsimp only
    rw [(eta2rho_hasDerivAt_right hr ht.1 ht.2).deriv]
    exact abs_of_nonpos (signR t ⟨ht.1.le, ht.2.le⟩)
  have iL : IntervalIntegrable (gL ρ) volume (1 / 4) (1 / 2) :=
    (gL_continuousOn hr).intervalIntegrable_of_Icc hL
  have iR : IntervalIntegrable (gR ρ) volume (1 / 2) 1 :=
    (gR_continuousOn hr).intervalIntegrable_of_Icc hR
  have iaL : IntervalIntegrable (fun t => |deriv (eta2rho ρ) t|) volume (1 / 4) (1 / 2) :=
    iL.congr_uIoo (by rw [uIoo_of_le hL]; exact eqL.symm)
  have iaR : IntervalIntegrable (fun t => |deriv (eta2rho ρ) t|) volume (1 / 2) 1 :=
    iR.neg.congr_uIoo (by rw [uIoo_of_le hR]; exact eqR.symm)
  have eL : (∫ t in (1 / 4 : ℝ)..(1 / 2), gL ρ t) =
      eta2rho ρ (1 / 2) - eta2rho ρ (1 / 4) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
      (eta2rho_continuous hr).continuousOn
      (fun t ht => eta2rho_hasDerivAt_left hr ht.1 ht.2) iL
  have eR : (∫ t in (1 / 2 : ℝ)..1, gR ρ t) = eta2rho ρ 1 - eta2rho ρ (1 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
      (eta2rho_continuous hr).continuousOn
      (fun t ht => eta2rho_hasDerivAt_right hr ht.1 ht.2) iR
  have hwhole : (∫ t, |deriv (eta2rho ρ) t|) =
      ∫ t in (1 / 4 : ℝ)..1, |deriv (eta2rho ρ) t| := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1 / 4 : ℝ) 1)]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hL.trans hR)]
    · intro t ht
      have hout : t < 1 / 4 ∨ 1 < t := by
        simpa only [mem_Icc, not_and_or, not_le] using ht
      rw [(eta2rho_hasDerivAt_out hout).deriv, abs_zero]
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals iaL iaR,
    intervalIntegral.integral_congr_Ioo_of_le hL eqL,
    intervalIntegral.integral_congr_Ioo_of_le hR eqR,
    intervalIntegral.integral_neg, eL, eR]
  have hq : eta2rho ρ (1 / 4) = 0 := by
    unfold eta2rho
    rw [eta2_of_mem_left (t := (1 / 4 : ℝ)) le_rfl (by norm_num)]
    norm_num
  have ho : eta2rho ρ 1 = 0 := by
    unfold eta2rho
    rw [eta2_of_mem_right (t := (1 : ℝ)) (by norm_num) le_rfl]
    norm_num
  rw [hq, ho]
  ring

/-- The second strict estimate of equation 2.6 and Lemma A.3. -/
theorem integral_abs_deriv_eta2rho_lt {ρ : ℝ} (hρ : 4 ≤ ρ) :
    (∫ t, |deriv (eta2rho ρ) t|) < 8 * Real.log 2 * Real.log ρ := by
  rw [integral_abs_deriv_eta2rho hρ]
  exact eta2rho_deriv_bound hρ

end LeanLab.HelfgottArcs

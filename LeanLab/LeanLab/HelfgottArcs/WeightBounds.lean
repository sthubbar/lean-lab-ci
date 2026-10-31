/-
Elementary weight bounds from Helfgott, arXiv 1205.5252v4.
Source: equation 1.4 on page 3 and equation 2.6 on page 7.
AI wrote this Lean code for CODEX task62.
Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Weights

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real Filter Topology

/-- The weight is positive exactly in the interior of its support. -/
theorem eta2_pos_iff (t : ℝ) : 0 < eta2 t ↔ t ∈ Ioo (1 / 4 : ℝ) 1 := by
  constructor
  · intro hp
    have hs := eta2_support (show t ∈ Function.support eta2 from ne_of_gt hp)
    constructor
    · rcases hs.1.lt_or_eq with h | h
      · exact h
      · have hz : eta2 t = 0 := by
          rw [← h, eta2_of_mem_left le_rfl (by norm_num)]; norm_num
        linarith
    · rcases hs.2.lt_or_eq with h | h
      · exact h
      · have hz : eta2 t = 0 := by
          rw [h, eta2_of_mem_right (by norm_num) le_rfl]; norm_num
        linarith
  · rintro ⟨h1, h2⟩
    rcases le_or_gt t (1 / 2) with h | h
    · rw [eta2_of_mem_left h1.le h]
      exact mul_pos (by norm_num) (Real.log_pos (by linarith))
    · rw [eta2_of_mem_right h.le h2.le]
      have hl := Real.log_neg (by linarith : (0 : ℝ) < t) h2
      nlinarith

/-- The zero extension of eta2 is continuous on the whole real line. -/
theorem eta2_continuous : Continuous eta2 := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : 0 < t
  · have hc : ContinuousAt (fun s : ℝ =>
        4 * max (Real.log 2 - |Real.log (2 * s)|) 0) t := by
      have hl : ContinuousAt (fun s : ℝ => Real.log (2 * s)) t :=
        (continuousAt_const.mul continuousAt_id).log (by dsimp; positivity)
      exact continuousAt_const.mul ((continuousAt_const.sub hl.abs).max continuousAt_const)
    apply hc.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact if_pos hs
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show t < 1 / 4 by linarith)] with s hs
    exact eta2_of_lt hs

/-- For rho at least 4, multiplying eta2 by log of rho times t preserves nonnegativity. -/
theorem eta2rho_nonneg {ρ : ℝ} (hρ : 4 ≤ ρ) (t : ℝ) : 0 ≤ eta2rho ρ t := by
  by_cases hz : eta2 t = 0
  · simp [eta2rho, hz]
  · have ht := eta2_support (show t ∈ Function.support eta2 from hz)
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hp : 1 ≤ ρ * t := by nlinarith [ht.1]
    exact mul_nonneg (Real.log_nonneg hp) (eta2_nonneg t)

/-- The logarithm weighted eta2 is continuous for every positive rho. -/
theorem eta2rho_continuous {ρ : ℝ} (hρ : 0 < ρ) : Continuous (eta2rho ρ) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : 0 < t
  · have hl : ContinuousAt (fun s : ℝ => Real.log (ρ * s)) t :=
      (continuousAt_const.mul continuousAt_id).log (by dsimp; positivity)
    exact hl.mul eta2_continuous.continuousAt
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show t < 1 / 4 by linarith)] with s hs
    simp [eta2rho, eta2_of_lt hs]

/-- Compact support gives integrability of eta2rho for every positive rho. -/
theorem eta2rho_integrable {ρ : ℝ} (hρ : 0 < ρ) : Integrable (eta2rho ρ) := by
  apply (eta2rho_continuous hρ).continuousOn.integrableOn_Icc.integrable_of_forall_notMem_eq_zero
    (s := Icc (1 / 4 : ℝ) 1)
  intro t ht
  have hz : eta2 t = 0 := by
    by_contra hn
    exact ht (eta2_support hn)
  simp [eta2rho, hz]

/-- The pointwise comparison used in the first line of equation 2.6. -/
theorem eta2rho_le_log_mul {ρ : ℝ} (hρ : 4 ≤ ρ) (t : ℝ) :
    eta2rho ρ t ≤ Real.log ρ * eta2 t := by
  by_cases hz : eta2 t = 0
  · simp [eta2rho, hz]
  · have ht := eta2_support (show t ∈ Function.support eta2 from hz)
    have hr : 0 < ρ := by linarith
    have ht0 : 0 < t := by linarith [ht.1]
    have hp : 0 < ρ * t := mul_pos hr ht0
    have hl : Real.log (ρ * t) ≤ Real.log ρ :=
      Real.log_le_log hp (by nlinarith [ht.2])
    exact mul_le_mul_of_nonneg_right hl (eta2_nonneg t)

/-- The first strict L1 estimate of equation 2.6, with the zero extension on the real line. -/
theorem integral_abs_eta2rho_lt {ρ : ℝ} (hρ : 4 ≤ ρ) :
    (∫ t, |eta2rho ρ t|) < Real.log ρ := by
  have hr : 0 < ρ := by linarith
  have hab : (1 / 4 : ℝ) < 1 := by norm_num
  have hout : ∀ t : ℝ, t ∉ Ioc (1 / 4 : ℝ) 1 → eta2rho ρ t = 0 := by
    intro t ht
    have hz : eta2 t = 0 := by
      apply le_antisymm _ (eta2_nonneg t)
      apply le_of_not_gt
      intro hp
      have hs := (eta2_pos_iff t).1 hp
      exact ht ⟨hs.1, hs.2.le⟩
    simp [eta2rho, hz]
  have hwhole : (∫ t, eta2rho ρ t) = ∫ t in (1 / 4 : ℝ)..1, eta2rho ρ t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (1 / 4 : ℝ) 1) hout,
      ← intervalIntegral.integral_of_le hab.le]
  have hmass : (∫ t in (1 / 4 : ℝ)..1, eta2 t) = 1 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals eta2_intervalIntegrable_left
      eta2_intervalIntegrable_right, integral_eta2_left, integral_eta2_right]
    ring
  have hc : ContinuousOn (fun t => Real.log ρ * eta2 t) (Icc (1 / 4 : ℝ) 1) :=
    continuousOn_const.mul eta2_continuous.continuousOn
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab (eta2rho_continuous hr).continuousOn hc
    (fun t _ => eta2rho_le_log_mul hρ t) ?_
  · have hn : (fun t => |eta2rho ρ t|) = eta2rho ρ :=
      funext fun t => abs_of_nonneg (eta2rho_nonneg hρ t)
    rw [hn, hwhole]
    rw [intervalIntegral.integral_const_mul, hmass, mul_one] at hi
    exact hi
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [eta2rho_half, eta2_half, Real.log_div hr.ne' (by norm_num)]
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith

end LeanLab.HelfgottArcs

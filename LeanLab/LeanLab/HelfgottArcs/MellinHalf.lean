/-
The actual Mellin half moment used to average the major arc error.
Source: https://arxiv.org/abs/1305.2897v4, page 48, proof of Corollary 4.9.
AI wrote this Lean code for CODEX task81. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.WeightBounds
import LeanLab.HelfgottMajor.Sec49

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real

/-- The Mellin half moment is the square of the eta1 half moment. -/
theorem integral_eta2_div_sqrt :
    (∫ t, eta2 t / √t) = (4 * (1 - 1 / √2)) ^ 2 := by
  have hL : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hR : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hc : ContinuousOn (fun t : ℝ => eta2 t / √t) (Ioi 0) :=
    eta2_continuous.continuousOn.div continuous_sqrt.continuousOn
      (fun t ht => (sqrt_pos.mpr ht).ne')
  have iL : IntervalIntegrable (fun t => eta2 t / √t) volume (1 / 4) (1 / 2) :=
    (hc.mono (fun t ht => show 0 < t from by linarith [ht.1])).intervalIntegrable_of_Icc hL
  have iR : IntervalIntegrable (fun t => eta2 t / √t) volume (1 / 2) 1 :=
    (hc.mono (fun t ht => show 0 < t from by linarith [ht.1])).intervalIntegrable_of_Icc hR
  have hdL (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s => 8 * √s * (log (4 * s) - 2)) (4 * log (4 * t) / √t) t := by
    have hs := Real.hasDerivAt_sqrt ht.ne'
    have hl := (((hasDerivAt_id' t).const_mul 4).log (by dsimp; positivity)).sub_const 2
    have hh := ((hs.const_mul 8).mul hl)
    apply hh.congr_deriv
    field_simp [(sqrt_pos.mpr ht).ne', ht.ne']
    nlinarith [sq_sqrt ht.le]
  have hdR (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s => -8 * √s * (log s - 2)) (-4 * log t / √t) t := by
    have hs := Real.hasDerivAt_sqrt ht.ne'
    have hl := (Real.hasDerivAt_log ht.ne').sub_const 2
    have hh := ((hs.const_mul (-8)).mul hl)
    apply hh.congr_deriv
    field_simp [(sqrt_pos.mpr ht).ne', ht.ne']
    nlinarith [sq_sqrt ht.le]
  have eqL : (∫ t in (1 / 4 : ℝ)..(1 / 2), eta2 t / √t) =
      8 * √(1 / 2 : ℝ) * (log (4 * (1 / 2 : ℝ)) - 2) -
        8 * √(1 / 4 : ℝ) * (log (4 * (1 / 4 : ℝ)) - 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => 8 * √s * (log (4 * s) - 2))
    · intro t ht
      rw [uIcc_of_le hL] at ht
      convert hdL t (by linarith [ht.1]) using 1
      rw [eta2_of_mem_left ht.1 ht.2]
    · exact iL
  have eqR : (∫ t in (1 / 2 : ℝ)..1, eta2 t / √t) =
      -8 * √(1 : ℝ) * (log 1 - 2) - -8 * √(1 / 2 : ℝ) * (log (1 / 2 : ℝ) - 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => -8 * √s * (log s - 2))
    · intro t ht
      rw [uIcc_of_le hR] at ht
      convert hdR t (by linarith [ht.1]) using 1
      rw [eta2_of_mem_right ht.1 ht.2]
    · exact iR
  have hwhole : (∫ t, eta2 t / √t) = ∫ t in (1 / 4 : ℝ)..1, eta2 t / √t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1 / 4 : ℝ) 1)]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hL.trans hR)]
    · intro t ht
      have hz : eta2 t = 0 := by
        by_contra hn
        exact ht (eta2_support hn)
      rw [hz, zero_div]
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals iL iR, eqL, eqR]
  have hhalf : √(1 / 2 : ℝ) = 1 / √2 := by rw [sqrt_div (by norm_num), sqrt_one]
  have hquarter : √(1 / 4 : ℝ) = 1 / 2 := by norm_num
  have hlog : log (1 / 2 : ℝ) = -log 2 := by
    rw [log_div (by norm_num) (by norm_num), log_one]
    ring
  rw [hhalf, hquarter, hlog]
  norm_num
  have hs : (√(2 : ℝ)) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hs0 : √(2 : ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
  field_simp
  nlinarith

/-- The actual averaging integral is at most the coefficient printed in Corollary 4.9. -/
theorem mellin_half_eta2_le :
    (∫ t in Ioi (0 : ℝ), eta2 t / √t) ≤ 1.37259 := by
  have he : (∫ t in Ioi (0 : ℝ), eta2 t / √t) = ∫ t, eta2 t / √t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have ht0 : t ≤ 0 := by simpa only [mem_Ioi, not_lt] using ht
    rw [eta2_of_lt (by linarith), zero_div]
  rw [he, integral_eta2_div_sqrt]
  exact LeanLab.HelfgottMajor.Sec49.mellin_half_le.1

end LeanLab.HelfgottArcs

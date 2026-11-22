import Mathlib
import LeanLab.PNTPort.StrongPNT.Rectangle

/-!
Audit of the fixed border logarithmic derivative input.
P0014 page 39 bounds the zero count. It does not state this contour input.
The numerical values at conductor 19 are recorded separately and remain CONDITIONAL.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.BorderAudit680

/-- The point shared by both middle regions belongs to the upper border. -/
theorem midpoint_mem_border :
    (⟨(1 / 2 : ℝ), (3 / 2 : ℝ)⟩ : ℂ) ∈
      RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ)
        (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ) := by
  norm_num [RectangleBorder, Complex.mem_reProdIm, Set.uIcc_of_le]

/-- Elementary obstruction from explicit bounds for a value and derivative.
No evaluation of a Dirichlet L function is asserted. -/
theorem norm_logDeriv_gt_of_small_value {f : ℂ → ℂ} {s : ℂ}
    (h0 : f s ≠ 0) (hv : ‖f s‖ ≤ 1 / 20) (hd : 1 ≤ ‖deriv f s‖) :
    0.5 * Real.log (19 : ℝ) + 11.7 < ‖logDeriv f s‖ := by
  have hlog : Real.log (19 : ℝ) ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at he
    linarith
  rw [logDeriv_apply, norm_div]
  have hn : 0 < ‖f s‖ := norm_pos_iff.mpr h0
  apply (lt_div_iff₀ hn).mpr
  have hb : 0 ≤ 0.5 * Real.log (19 : ℝ) + 11.7 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 19 by norm_num)
    linarith
  have hm := mul_le_mul_of_nonneg_left hv hb
  nlinarith

/-- Conditional rejection of a uniform conductor 19 border bound from explicit value data. -/
theorem not_border_bound_of_value_data {f : ℂ → ℂ}
    (h0 : f (⟨(1 / 2 : ℝ), (3 / 2 : ℝ)⟩ : ℂ) ≠ 0)
    (hv : ‖f (⟨(1 / 2 : ℝ), (3 / 2 : ℝ)⟩ : ℂ)‖ ≤ 1 / 20)
    (hd : 1 ≤ ‖deriv f (⟨(1 / 2 : ℝ), (3 / 2 : ℝ)⟩ : ℂ)‖) :
    ¬ ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ)
      (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      ‖logDeriv f u‖ ≤ 0.5 * Real.log (19 : ℝ) + 11.7 := by
  intro h
  exact (not_le_of_gt (norm_logDeriv_gt_of_small_value h0 hv hd))
    (h _ midpoint_mem_border)

end LeanLab.HelfgottMajor.BorderAudit680

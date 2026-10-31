/-
The beta integral bound in P0029 page 24 display 6.9.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- Page 24 display 6.9. The norm of the beta factor is bounded by the real beta integral. -/
theorem betaC_norm_integral150 {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖betaC u v‖ ≤ ∫ x in (0 : ℝ)..1, x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
  rw [betaC, ← Complex.betaIntegral_eq_Gamma_mul_div u v hu hv]
  unfold Complex.betaIntegral
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq ?_
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
  intro x hm
  dsimp only
  have hx1 : 0 < 1 - x := sub_pos.mpr hm.2
  have hcast : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hm.1,
    Complex.norm_cpow_eq_rpow_re_of_pos hx1]
  simp only [Complex.sub_re, Complex.one_re]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.betaC_norm_integral150

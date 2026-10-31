/-
Weighted beta change of scale from page 29 display 7.21.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Archimedean

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. Page 29 display 7.21. The sigma substitution with its Jacobian v.
This is the weighted form of Mathlib Complex.betaIntegral_scaled. -/
theorem beta_scaling107 (ϕ : ℝ → ℝ) (N : ℝ) {v : ℝ} (hv : 0 < v) (ρ₁ ρ₂ : ℂ) :
    (∫ u in (0 : ℝ)..v, ((ϕ (u / N) * ϕ ((v - u) / N) : ℝ) : ℂ) *
      (u : ℂ) ^ (ρ₁ - 1) * ((v - u : ℝ) : ℂ) ^ (ρ₂ - 1)) =
      (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * Jphi ϕ N v ρ₁ ρ₂ := by
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hpow : (v : ℂ) ^ (ρ₁ + ρ₂ - 1) =
      v * ((v : ℂ) ^ (ρ₁ - 1) * (v : ℂ) ^ (ρ₂ - 1)) := by
    rw [(by abel : ρ₁ + ρ₂ - 1 = 1 + (ρ₁ - 1) + (ρ₂ - 1)),
      Complex.cpow_add _ _ hv', Complex.cpow_add 1 _ hv', Complex.cpow_one, mul_assoc]
  unfold Jphi
  rw [hpow, mul_assoc, ← intervalIntegral.integral_const_mul, ← Complex.real_smul,
    ← zero_div v, ← div_self hv.ne', ← intervalIntegral.integral_comp_div _ hv.ne', zero_div]
  simp_rw [intervalIntegral.integral_of_le hv.le]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have h1 : (v : ℂ) ^ (ρ₁ - 1) * ((u / v : ℝ) : ℂ) ^ (ρ₁ - 1) =
      (u : ℂ) ^ (ρ₁ - 1) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hv.le (div_pos hu.1 hv).le]
    congr 1
    push_cast
    field_simp
  have h2 : (v : ℂ) ^ (ρ₂ - 1) * ((1 - u / v : ℝ) : ℂ) ^ (ρ₂ - 1) =
      ((v - u : ℝ) : ℂ) ^ (ρ₂ - 1) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hv.le
      (sub_nonneg.mpr ((div_le_one hv).mpr hu.2))]
    congr 1
    push_cast
    field_simp
    <;> ring
  have hscale : v * (u / v) = u := mul_div_cancel₀ u hv.ne'
  have hscale' : v * (1 - u / v) = v - u := by rw [mul_sub, mul_one, hscale]
  simp only [div_self hv.ne', hscale, hscale']
  rw [← h1, ← h2]
  ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.beta_scaling107

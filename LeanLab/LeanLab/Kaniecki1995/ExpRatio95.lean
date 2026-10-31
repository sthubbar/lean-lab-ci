/-
P0022, page 365, the elementary inequality 10.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.Statements

namespace LeanLab.Kaniecki1995.ExpRatio95
open Real Complex Finset

/-- Page 365, inequality 10. The norm of the exponential difference quotient
is at most one over one minus half of the norm. Lean assigns zero at s equal to zero. -/
theorem exp_ratio_bound {s : ℂ} (hs : ‖s‖ < 2) :
    ‖(Complex.exp s - 1) / s‖ ≤ 1 / (1 - ‖s‖ / 2) := by
  by_cases h0 : s = 0
  · subst s
    norm_num
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr h0
  have hd : 0 < 1 - ‖s‖ / 2 := by linarith
  have h1 := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum s 1
  simp only [sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h1
  have h2 := Real.exp_le_two_add_div_two_sub hn.le hs
  rw [norm_div, div_le_iff₀ hn]
  have heq : (2 + ‖s‖) / (2 - ‖s‖) - 1 = ‖s‖ / (1 - ‖s‖ / 2) := by
    field_simp
    <;> ring
  calc ‖Complex.exp s - 1‖ ≤ Real.exp ‖s‖ - 1 := h1
    _ ≤ (2 + ‖s‖) / (2 - ‖s‖) - 1 := sub_le_sub_right h2 1
    _ = ‖s‖ / (1 - ‖s‖ / 2) := heq
    _ = 1 / (1 - ‖s‖ / 2) * ‖s‖ := by ring

/-- Pages 365 and 366, inequality 10 after scaling by a nonnegative delta. -/
theorem exp_scaled_bound {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ} (hs : δ * ‖s‖ < 2) :
    ‖(Complex.exp ((δ : ℂ) * s) - 1) / s‖ ≤ δ / (1 - δ * ‖s‖ / 2) := by
  by_cases h0 : δ = 0
  · subst δ
    simp
  have hδ0 : 0 < δ := lt_of_le_of_ne hδ (Ne.symm h0)
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast h0
  have hn : ‖(δ : ℂ) * s‖ = δ * ‖s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
  have h := exp_ratio_bound (s := (δ : ℂ) * s) (by rwa [hn])
  have heq : (Complex.exp ((δ : ℂ) * s) - 1) / s =
      (δ : ℂ) * ((Complex.exp ((δ : ℂ) * s) - 1) / ((δ : ℂ) * s)) := by
    by_cases hs0 : s = 0
    · simp [hs0]
    · field_simp
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
  rw [hn] at h
  exact (mul_le_mul_of_nonneg_left h hδ).trans_eq (by ring)

/-- Page 365, inequality 10. The quotient bound has a concrete admissible argument. -/
theorem exp_ratio_instance : ‖(((1 : ℝ) / 2 : ℝ) : ℂ)‖ < 2 := by
  norm_num

/-- Page 367, inequality 12. The numerator is at most two plus the reciprocal of T. -/
theorem exp_numerator_bound {T σ : ℝ} (hT : 0 < T) (hσ : σ ≤ 1) (t : ℝ) :
    ‖Complex.exp ((Real.log (1 + 1 / T) : ℂ) * ((σ : ℂ) + t * I)) - 1‖ ≤
      2 + 1 / T := by
  have hd : 0 ≤ Real.log (1 + 1 / T) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hm : Real.log (1 + 1 / T) * σ ≤ Real.log (1 + 1 / T) :=
    mul_le_of_le_one_right hd hσ
  have h := Real.exp_le_exp.mpr hm
  rw [Real.exp_log (by positivity)] at h
  calc ‖Complex.exp ((Real.log (1 + 1 / T) : ℂ) * ((σ : ℂ) + t * I)) - 1‖ ≤
      ‖Complex.exp ((Real.log (1 + 1 / T) : ℂ) * ((σ : ℂ) + t * I))‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
    _ = Real.exp (Real.log (1 + 1 / T) * σ) + 1 := by simp [Complex.norm_exp]
    _ ≤ 2 + 1 / T := by linarith

/-- Page 368, inequality 15. Integrating the exponential along a real segment
bounds the quotient by delta times the exponential of delta Re s. -/
theorem quotient_exponential {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Complex.exp ((δ : ℂ) * s) - 1) / s‖ ≤ δ * Real.exp (δ * s.re) := by
  by_cases hs0 : s = 0
  · subst s
    simpa using hδ
  have heq : (Complex.exp ((δ : ℂ) * s) - 1) / s =
      ∫ u in (0 : ℝ)..δ, Complex.exp (s * u) := by
    rw [integral_exp_mul_complex hs0]
    simp [mul_comm]
  rw [heq]
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) δ,
      ‖Complex.exp (s * u)‖ ≤ Real.exp (δ * s.re) := by
    intro u hu
    rw [Set.uIoc_of_le hδ] at hu
    rw [Complex.norm_exp]
    have hmul := mul_le_mul_of_nonneg_left hu.2 hs
    simpa [mul_comm] using Real.exp_le_exp.mpr hmul
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa [abs_of_nonneg hδ, mul_comm] using hb

end LeanLab.Kaniecki1995.ExpRatio95

#print axioms LeanLab.Kaniecki1995.ExpRatio95.exp_ratio_bound
#print axioms LeanLab.Kaniecki1995.ExpRatio95.exp_ratio_instance

#print axioms LeanLab.Kaniecki1995.ExpRatio95.exp_scaled_bound

#print axioms LeanLab.Kaniecki1995.ExpRatio95.exp_numerator_bound

#print axioms LeanLab.Kaniecki1995.ExpRatio95.quotient_exponential

import LeanLab.ChirreHagen2025.Statements

/-!
Chandee Appendix page 13, the logarithmic integral in the first Binet
head estimate. Mathlib's logarithm series and Basel sum give its value.
https://arxiv.org/abs/0906.4177
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.LogKernel429
open MeasureTheory

/-- Chandee page 13, the positive logarithmic comparison kernel. -/
noncomputable def logKernel (u : ℝ) : ℝ :=
  Real.log (1 / (1 - Real.exp (-2 * Real.pi * u)))

/-- Chandee page 13, the nth nonnegative logarithm series term. -/
noncomputable def term (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * u) / ((n : ℝ) + 1)

/-- Chandee page 13, elementary exponential term integrability and evaluation. -/
theorem term_integral (n : ℕ) :
    IntegrableOn (term n) (Set.Ioi (0 : ℝ)) ∧
    (∫ u in Set.Ioi (0 : ℝ), term n u) = 1 / (2 * Real.pi * ((n : ℝ) + 1) ^ 2) := by
  have ha : -(2 * Real.pi * ((n : ℝ) + 1)) < 0 := by
    have h : 0 < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
    linarith
  constructor
  · exact (integrableOn_exp_mul_Ioi ha 0).div_const _
  · unfold term
    rw [integral_div, integral_exp_mul_Ioi ha 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp

/-- Chandee page 13, the logarithm series on the positive half line. -/
theorem term_hasSum (u : ℝ) (hu : 0 < u) :
    HasSum (fun n : ℕ => term n u) (logKernel u) := by
  have hr : |Real.exp (-2 * Real.pi * u)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hh := Real.hasSum_pow_div_log_of_abs_lt_one hr
  convert hh using 1
  · funext n
    unfold term
    rw [← Real.exp_nat_mul]
    push_cast
    congr 2
    ring
  · unfold logKernel
    rw [one_div, Real.log_inv]

/-- Chandee page 13, nonnegativity on the actual integration domain. -/
theorem log_kernel_nonneg (u : ℝ) (hu : 0 < u) : 0 ≤ logKernel u := by
  rw [← (term_hasSum u hu).tsum_eq]
  apply tsum_nonneg
  intro n
  unfold term
  positivity

/-- Chandee page 13, exact logarithmic integral from the Basel sum.
Termwise integration is justified by summability of the integral norms. -/
theorem log_kernel_integral :
    (∫ u in Set.Ioi (0 : ℝ), logKernel u) = Real.pi / 12 := by
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have hs := hasSum_zeta_two.summable
    have ht := hs.tsum_eq_zero_add
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero, zero_add] at ht
    simp only [Nat.cast_add, Nat.cast_one] at ht
    have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
    have hv : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 6 := by
      rw [← ht]
      exact hasSum_zeta_two.tsum_eq
    simpa only [hv] using hshift.hasSum
  have hc : HasSum (fun n : ℕ => 1 / (2 * Real.pi * ((n : ℝ) + 1) ^ 2)) (Real.pi / 12) := by
    convert hz.mul_left (1 / (2 * Real.pi)) using 1
    · funext n
      field_simp
    · field_simp
      ring
  have hi (n : ℕ) : Integrable (term n) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (term_integral n).1
  have hn (n : ℕ) : (∫ u in Set.Ioi (0 : ℝ), ‖term n u‖) =
      1 / (2 * Real.pi * ((n : ℝ) + 1) ^ 2) := by
    have heq : (fun u : ℝ => ‖term n u‖) = term n := by
      funext u
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold term; positivity)]
    rw [heq]
    exact (term_integral n).2
  have hnorm : Summable (fun n : ℕ => ∫ u in Set.Ioi (0 : ℝ), ‖term n u‖) := by
    simp_rw [hn]
    exact hc.summable
  have hsum := hasSum_integral_of_summable_integral_norm hi hnorm
  have hval : (∫ u in Set.Ioi (0 : ℝ), ∑' n : ℕ, term n u) = Real.pi / 12 := by
    apply hsum.unique
    simpa only [(term_integral _).2] using hc
  calc
    _ = ∫ u in Set.Ioi (0 : ℝ), ∑' n : ℕ, term n u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact (term_hasSum u hu).tsum_eq.symm
    _ = _ := hval

/-- Chandee page 13, actual integrability of the logarithmic kernel. -/
theorem log_kernel_integrable : IntegrableOn logKernel (Set.Ioi (0 : ℝ)) := by
  apply Integrable.of_integral_ne_zero
  rw [log_kernel_integral]
  positivity

end LeanLab.ChirreHagen2025.LogKernel429

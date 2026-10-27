/-
The Gaussian squared norm in Helfgott, arXiv:1312.7748v2, printed page 61.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import Mathlib

open Real MeasureTheory Set

namespace LeanLab.Helfgott2013.GaussianL2

/-- The exact fourth Gaussian moment on the positive half line. -/
theorem fourth_moment :
    (∫ t in Ioi (0 : ℝ), t ^ 4 * Real.exp (-t ^ 2)) = 3 / 8 * Real.sqrt Real.pi := by
  have hg : Real.Gamma (5 / 2) = 3 / 4 * Real.sqrt Real.pi := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hi := Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 5 / 2)
  rw [← integral_comp_rpow_Ioi_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
  have he : (∫ t in Ioi (0 : ℝ), (2 * t ^ ((2 : ℝ) - 1)) •
      (Real.exp (-(t ^ (2 : ℝ))) * (t ^ (2 : ℝ)) ^ ((5 / 2 : ℝ) - 1))) =
      2 * ∫ t in Ioi (0 : ℝ), t ^ 4 * Real.exp (-t ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    dsimp only
    rw [← Real.rpow_mul ht0.le]
    norm_num [smul_eq_mul]
    ring
  rw [he, hg] at hi
  linarith

#print axioms fourth_moment

/-- The Gaussian smoothing function used in Section 7.2. -/
noncomputable def phi (t : ℝ) : ℝ := t ^ 2 * Real.exp (-t ^ 2 / 2)

/-- The squared norm of phi is the fourth Gaussian moment. -/
theorem phi_sq_integral :
    (∫ t in Ioi (0 : ℝ), phi t ^ 2) = 3 / 8 * Real.sqrt Real.pi := by
  have he (t : ℝ) : phi t ^ 2 = t ^ 4 * Real.exp (-t ^ 2) := by
    unfold phi
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1 <;> ring
  simp_rw [he]
  exact fourth_moment

#print axioms phi_sq_integral

/-- The squared Gaussian smoothing function is integrable. -/
theorem phi_sq_integrable : IntegrableOn (fun t : ℝ => phi t ^ 2) (Ioi 0) := by
  by_contra hc
  have he := phi_sq_integral
  rw [integral_undef hc] at he
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  nlinarith

#print axioms phi_sq_integrable

/-- The exact mass of the Gaussian smoothing function. -/
theorem phi_integral :
    (∫ t in Ioi (0 : ℝ), phi t) = Real.sqrt (Real.pi / 2) := by
  have hg : Real.Gamma (3 / 2) = 1 / 2 * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← integral_comp_rpow_Ioi_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
  have he : (∫ t in Ioi (0 : ℝ), (2 * t ^ ((2 : ℝ) - 1)) •
      ((t ^ (2 : ℝ)) ^ ((3 / 2 : ℝ) - 1) * Real.exp (-(1 / 2 * t ^ (2 : ℝ))))) =
      2 * ∫ t in Ioi (0 : ℝ), phi t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    dsimp only
    rw [← Real.rpow_mul ht0.le]
    norm_num [smul_eq_mul, phi]
    ring_nf
  rw [he, hg] at hi
  have hp : ((1 / (1 / 2) : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have heq : (∫ t in Ioi (0 : ℝ), phi t) =
      (1 / (1 / 2) : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt Real.pi / 4 := by
    linarith
  have hs : (∫ t in Ioi (0 : ℝ), phi t) ^ 2 = Real.pi / 2 := by
    rw [heq, div_pow, mul_pow, hp, Real.sq_sqrt Real.pi_pos.le]
    ring
  have hnonneg : 0 ≤ ∫ t in Ioi (0 : ℝ), phi t := integral_nonneg (fun t => by
    unfold phi
    positivity)
  apply (sq_eq_sq₀ hnonneg (Real.sqrt_nonneg _)).mp
  rw [hs, Real.sq_sqrt (by positivity)]

#print axioms phi_integral

/-- The Gaussian smoothing function is integrable on the positive half line. -/
theorem phi_integrable : IntegrableOn phi (Ioi (0 : ℝ)) := by
  by_contra hc
  have he := phi_integral
  rw [integral_undef hc] at he
  have hp : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  linarith

#print axioms phi_integrable

end LeanLab.Helfgott2013.GaussianL2

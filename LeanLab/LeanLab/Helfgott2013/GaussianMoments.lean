/-
Gaussian moment inputs for Helfgott, arXiv:1312.7748v2, display 7.11 on page 58.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import LeanLab.Helfgott2013.GaussianL2

open Real MeasureTheory Set

namespace LeanLab.Helfgott2013.GaussianMoments
open GaussianL2

/-- The exact Gamma formula for every nonnegative integer moment of phi. -/
theorem phi_moment (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), phi t * t ^ k) =
      (1 / (1 / 2) : ℝ) ^ (((k : ℝ) + 3) / 2) * Real.Gamma (((k : ℝ) + 3) / 2) / 2 := by
  have ha : (0 : ℝ) < ((k : ℝ) + 3) / 2 := by positivity
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← integral_comp_rpow_Ioi_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
  have he : (∫ t in Ioi (0 : ℝ), (2 * t ^ ((2 : ℝ) - 1)) •
      ((t ^ (2 : ℝ)) ^ ((((k : ℝ) + 3) / 2) - 1) *
        Real.exp (-(1 / 2 * t ^ (2 : ℝ))))) =
      2 * ∫ t in Ioi (0 : ℝ), phi t * t ^ k := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    have hx : (t ^ (2 : ℝ)) ^ ((((k : ℝ) + 3) / 2) - 1) = t ^ (k + 1) := by
      rw [← Real.rpow_mul ht0.le]
      have he : (2 : ℝ) * ((((k : ℝ) + 3) / 2) - 1) = ((k + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [he, Real.rpow_natCast]
    dsimp only
    rw [hx]
    norm_num [smul_eq_mul, phi, pow_succ]
    ring_nf
  rw [he] at hi
  linarith

#print axioms phi_moment

/-- Every nonnegative integer Gaussian smoothing moment is integrable. -/
theorem phi_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => phi t * t ^ k) (Ioi 0) := by
  by_contra hc
  have he := phi_moment k
  rw [integral_undef hc] at he
  have hg : 0 < Real.Gamma (((k : ℝ) + 3) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hp : 0 < (1 / (1 / 2) : ℝ) ^ (((k : ℝ) + 3) / 2) *
      Real.Gamma (((k : ℝ) + 3) / 2) / 2 := by positivity
  linarith

#print axioms phi_moment_integrable

/-- The first Gaussian smoothing moment used in the quadratic calculation. -/
theorem phi_first_moment : (∫ t in Ioi (0 : ℝ), phi t * t) = 2 := by
  have h := phi_moment 1
  norm_num [Real.Gamma_add_one, Real.Gamma_one] at h
  exact h

#print axioms phi_first_moment

/-- The second Gaussian smoothing moment used in the quadratic calculation. -/
theorem phi_second_moment :
    (∫ t in Ioi (0 : ℝ), phi t * t ^ 2) = 3 * Real.sqrt (Real.pi / 2) := by
  have h0 := phi_moment 0
  have h2 := phi_moment 2
  norm_num only [Nat.cast_zero, Nat.cast_ofNat, zero_add, pow_zero, mul_one,
    one_div_div, div_self, OfNat.ofNat_ne_zero] at h0 h2
  have hp : (2 : ℝ) ^ (5 / 2 : ℝ) = 2 * (2 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  have hg : Real.Gamma (5 / 2) = 3 / 2 * Real.Gamma (3 / 2) := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  rw [phi_integral] at h0
  rw [h2, hp, hg]
  nlinarith [h0]

#print axioms phi_second_moment

end LeanLab.Helfgott2013.GaussianMoments

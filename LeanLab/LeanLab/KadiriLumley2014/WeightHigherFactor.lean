/-
P0059 arXiv 1407.7902v1 page 10, Lemma 3.1 final line.
Journal INTEGERS 14 A61 page 13 equation 69.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.WeightL2
import LeanLab.KadiriLumley2014.WeightCauchy

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- The normalized m-th derivative factor in equation 2.21. -/
noncomputable def higherFactor (m : ℕ) (δ : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ (m + 1) * |iteratedDeriv m (weight m) t|) /
    (∫ t in (0 : ℝ)..1, weight m t)

/-- The paper's polynomial weight is smooth to every order. -/
theorem weight_contDiff (m : ℕ) : ContDiff ℝ ⊤ (weight m) := by
  unfold weight
  fun_prop

/-- Exact m-th derivative norm divided by the mass. -/
theorem sqrt_derivative_norm_div_mass (m : ℕ) :
    Real.sqrt ((2 ^ (2 * m) * (m.factorial : ℝ)) ^ 2 / (2 * m + 1)) /
      (∫ t in (0 : ℝ)..1, weight m t) =
      (2 * m + 1).factorial / ((m.factorial : ℝ) * Real.sqrt (2 * m + 1)) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity), weight_mass]
  have hs : Real.sqrt (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The final lambda in Lemma 3.1. -/
noncomputable def lambdaHigher (m : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (((1 + δ) ^ (2 * m + 3) - 1) / (δ * (2 * m + 3))) *
    (2 * m + 1).factorial / ((m.factorial : ℝ) * Real.sqrt (2 * m + 1))

/-- Lemma 3.1 final line for every positive delta. -/
theorem higher_factor_bound (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    higherFactor m δ ≤ lambdaHigher m δ := by
  have hd : Continuous (iteratedDeriv m (weight m)) :=
    (weight_contDiff m).continuous_iteratedDeriv m (by simp)
  have hf : Continuous (fun t : ℝ => (1 + δ * t) ^ (m + 1)) := by fun_prop
  have hc := integral_mul_le_sqrt hf hd.abs
  have hpow : (fun t : ℝ => ((1 + δ * t) ^ (m + 1)) ^ 2) =
      (fun t => (1 + δ * t) ^ (2 * m + 2)) := by
    funext t
    rw [← pow_mul]
    congr 1
    omega
  simp_rw [sq_abs] at hc
  rw [hpow, integral_affine_pow _ hδ.ne', weight_mth_derivative_sq_integral] at hc
  have hn : 2 * m + 2 + 1 = 2 * m + 3 := by omega
  rw [hn] at hc
  push_cast at hc
  have hdiv := (div_le_div_iff_of_pos_right (weight_mass_pos m)).mpr hc
  unfold higherFactor lambdaHigher
  refine hdiv.trans_eq ?_
  rw [mul_div_assoc, sqrt_derivative_norm_div_mass]
  ring

end LeanLab.KadiriLumley2014.Task64

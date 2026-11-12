/-
Cauchy Schwarz support for PP1993 page 44 display 3.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
Mathlib Holder supplies the integral inequality.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.MinorData489

namespace LeanLab.Languasco2004.CoefficientGlue489
open Real MeasureTheory
noncomputable section

/-- Page 44 display 3: the squared real nonnegative integral form of
Cauchy Schwarz. Both square integrability hypotheses remain explicit. -/
theorem integral_cauchy_squared {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff]) hf0 hg0
    (by simpa using hf) (by simpa using hg)
  have hroot : (∫ x, f x * g x ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hHolder
  have hi0 : 0 ≤ ∫ x, f x * g x ∂μ := integral_nonneg_of_ae
    (by filter_upwards [hf0, hg0] with x hx hy using mul_nonneg hx hy)
  calc (∫ x, f x * g x ∂μ) ^ 2 ≤
      (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ hi0 hroot 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
        Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

/-- Page 44 display 3: two Cauchy Schwarz bounds compose to the cubic
prime weight factor. This is scalar glue, independent of Fourier sums. -/
theorem two_cauchy_bounds {E₁ E₂ K I J : ℝ}
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hK : 0 ≤ K) (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (houter : I ^ 2 ≤ E₁ * E₂) (hinner : J ≤ I * Real.sqrt (E₁ * K)) :
    J ^ 2 ≤ E₁ ^ 2 * E₂ * K := by
  calc J ^ 2 ≤ (I * Real.sqrt (E₁ * K)) ^ 2 := pow_le_pow_left₀ hJ hinner 2
    _ = I ^ 2 * (E₁ * K) := by rw [mul_pow, Real.sq_sqrt (mul_nonneg hE₁ hK)]
    _ ≤ (E₁ * E₂) * (E₁ * K) := mul_le_mul_of_nonneg_right houter (mul_nonneg hE₁ hK)
    _ = E₁ ^ 2 * E₂ * K := by ring

/-- Page 44 display 3: square roots can be removed from any nonnegative
uniform kernel bound. This is the pointwise inner Cauchy Schwarz step. -/
theorem inner_bound_of_square {E K J : ℝ} (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hJ : 0 ≤ J) (hsq : J ^ 2 ≤ E * K) : J ≤ Real.sqrt (E * K) := by
  exact (Real.le_sqrt hJ (mul_nonneg hE hK)).mpr hsq

#print axioms integral_cauchy_squared
#print axioms two_cauchy_bounds
#print axioms inner_bound_of_square
end
end LeanLab.Languasco2004.CoefficientGlue489

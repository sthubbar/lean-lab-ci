/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 50, 59, 60 and 63.
Independent first moment split. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420e
import LeanLab.Helfgott2013.MellinL1
namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- The eta star weight at the fixed scale 49.
Helfgott page 59 equation 7.15 and page 60 equation 7.20. -/
noncomputable def starWeight (t : ℝ) : ℝ :=
  LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2 (49 * t)

/-- The norm of the eta star Fourier sum.
Helfgott page 50 weighted triangle step. -/
noncomputable def starNorm (x α : ℝ) : ℝ :=
  ‖LeanLab.HelfgottArcs.S starWeight α x‖


/-- The compact eta two weight is nonnegative.
Helfgott page 25 equation 4.10 and the definition of eta two. -/
theorem eta2_nonneg (t : ℝ) : 0 ≤ LeanLab.HelfgottArcs.eta2 t := by
  unfold LeanLab.HelfgottArcs.eta2
  split_ifs <;> positivity

/-- The Gaussian phi weight is nonnegative.
Helfgott page 59 definition before equation 7.16. -/
theorem phi_nonneg (t : ℝ) : 0 ≤ LeanLab.HelfgottArcs.etaT2 t := by
  unfold LeanLab.HelfgottArcs.etaT2
  split_ifs <;> positivity

/-- The actual Mellin smoothing is nonnegative.
Helfgott page 60 equation 7.19 and the multiplicative convolution definition. -/
theorem etaStar_nonneg (t : ℝ) :
    0 ≤ LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2 t := by
  unfold LeanLab.HelfgottArcs.mconv
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact div_nonneg (mul_nonneg (eta2_nonneg y) (phi_nonneg _)) hy.le

/-- The absolute eta star Fourier sum is at most its nonnegative coefficient mass.
Helfgott page 50 first bound after the weighted triangle step. -/
theorem starNorm_le_mass {x : ℝ} (hx : 0 < x) (α : ℝ) :
    starNorm x α ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
        LeanLab.HelfgottArcs.etaT2 (49 * (n / x)) := by
  unfold starNorm starWeight
  rw [Task420.S_eq_charSeries]
  unfold Task420.charSeries
  have hcoeff (n : ℕ) :
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
            LeanLab.HelfgottArcs.etaT2 (49 * (n / x)) : ℂ) *
          LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ =
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
            LeanLab.HelfgottArcs.etaT2 (49 * (n / x)) := by
    rw [norm_mul, LeanLab.Ternary.MMS.norm_e, mul_one, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_nonneg (etaStar_nonneg _)]
  have hs : Summable fun n : ℕ =>
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
            LeanLab.HelfgottArcs.etaT2 (49 * (n / x)) : ℂ) *
          LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ := by
    simpa only [norm_mul, LeanLab.Ternary.MMS.norm_e, mul_one] using
      Task420.etaStar_coefficients_summable hx
  simpa only [hcoeff] using norm_tsum_le_tsum_norm hs

/-- The mass of the fixed eta star smoothing.
Helfgott page 60 equation 7.20, from the Mellin convolution mass formula,
the eta two integral one and the Gaussian phi integral sqrt pi over two. -/
theorem starWeight_integral :
    (∫ t in Set.Ioi (0 : ℝ), starWeight t) =
      Real.sqrt (Real.pi / 2) / LeanLab.Helfgott2013.κ := by
  have heq : (∫ t in Set.Ioi (0 : ℝ), starWeight t) =
      ∫ t in Set.Ioi (0 : ℝ), LeanLab.Helfgott2013.MellinL2.mellin (49 * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact Task420.etaStar_eq_mellin (mul_nonneg (by norm_num) (le_of_lt ht))
  rw [heq]
  have h := integral_comp_mul_left_Ioi LeanLab.Helfgott2013.MellinL2.mellin
    0 (by norm_num : (0 : ℝ) < 49)
  simpa [LeanLab.Helfgott2013.MellinL1.mellin_integral.2,
    LeanLab.Helfgott2013.κ, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- LEAF. The arithmetic first moment differs from its integral main term
by the explicit error at the fixed scale 49.
Helfgott page 59 equation 7.16 and page 63 display before equation 7.27.
This statement estimates the error alone and does not evaluate the integral. -/
theorem star_mass_error (x : ℝ) (hx : 4.9e26 ≤ x) :
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * starWeight (n / x)) -
      x * (∫ t in Set.Ioi (0 : ℝ), starWeight t)| ≤
      1.9075e-8 * x / LeanLab.Helfgott2013.κ := by
  sorry

/-- The explicit first moment follows from the mass identity and error bound.
Helfgott page 63 display before equation 7.27.
CONDITIONAL ON star_mass_error. -/
theorem star_mass_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
        LeanLab.HelfgottArcs.etaT2 (49 * (n / x))) ≤
      (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / LeanLab.Helfgott2013.κ := by
  have h := (abs_le.mp (star_mass_error x hx)).2
  rw [starWeight_integral] at h
  change (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * starWeight (n / x)) ≤ _
  calc
    _ ≤ x * (Real.sqrt (Real.pi / 2) / LeanLab.Helfgott2013.κ) +
        1.9075e-8 * x / LeanLab.Helfgott2013.κ := by linarith
    _ = _ := by ring

/-- The first moment bound supplies the required L infinity estimate.
Helfgott page 50 and page 63 before equation 7.27.
CONDITIONAL ON star_mass_upper. -/
theorem starNorm_uniform (x : ℝ) (hx : 4.9e26 ≤ x) (α : ℝ) :
    starNorm x α ≤ (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x /
      LeanLab.Helfgott2013.κ := by
  exact (starNorm_le_mass (by linarith) α).trans (star_mass_upper x hx)

end LeanLab.Ternary.Task580

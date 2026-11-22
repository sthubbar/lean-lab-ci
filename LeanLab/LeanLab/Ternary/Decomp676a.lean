/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 50 and 63.
The zero phase is the exact nonnegative eta star coefficient mass.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp580c

namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- The zero phase star norm equals the arithmetic first moment.
Helfgott page 63 display before equation 7.27. -/
theorem starNorm_zero_eq_mass (x : ℝ) :
    starNorm x 0 = ∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) * starWeight (n / x) := by
  have hm : 0 ≤ ∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) * starWeight (n / x) := by
    apply tsum_nonneg
    intro n
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (etaStar_nonneg _)
  unfold starNorm
  rw [Task420.S_eq_charSeries]
  unfold Task420.charSeries
  simp only [mul_zero, LeanLab.Ternary.MMS.e, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  have he : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (starWeight (n / x) : ℂ)) =
      ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * starWeight (n / x) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_tsum, Complex.ofReal_mul]
  rw [he]
  exact Complex.norm_of_nonneg hm

/-- The zero phase bounds every star phase at a positive scale.
Helfgott page 50 triangle inequality and page 51 last display. -/
theorem starNorm_le_zero {x : ℝ} (hx : 0 < x) (α : ℝ) :
    starNorm x α ≤ starNorm x 0 := by
  rw [starNorm_zero_eq_mass]
  exact starNorm_le_mass hx α

/-- The exact remainder coefficient mass gives the weighted minor moment bound.
Helfgott page 51 last display. No explicit arithmetic error estimate is used. -/
theorem remainder_moment_le_zero_mul_coeff_square {x : ℝ} (hx : 0 < x) :
    (∫ α in minorDomain x, starNorm x α * ‖remainderSeries x α‖ ^ 2) ≤
      starNorm x 0 * (∑' n : ℕ, ‖remainderCoeff x n‖ ^ 2) := by
  have hi : IntegrableOn (fun α => ‖remainderSeries x α‖ ^ 2)
      (Set.Ioc (0 : ℝ) 1) :=
    ((remainderSeries_continuous hx).norm.pow 2).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hsub : minorDomain x ⊆ Set.Ioc (0 : ℝ) 1 := Set.sdiff_subset
  have hmono := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖remainderSeries x α‖))
    (Filter.Eventually.of_forall hsub)
  have hw : IntegrableOn (fun α => starNorm x α * ‖remainderSeries x α‖ ^ 2)
      (minorDomain x) :=
    (((starNorm_continuous hx).mul ((remainderSeries_continuous hx).norm.pow 2)).integrableOn_Icc).mono_set
      (hsub.trans Set.Ioc_subset_Icc_self)
  have hle := integral_mono hw ((hi.mono_set hsub).const_mul (starNorm x 0))
    (fun α => mul_le_mul_of_nonneg_right (starNorm_le_zero hx α) (sq_nonneg _))
  rw [integral_const_mul] at hle
  calc
    _ ≤ starNorm x 0 * (∫ α in minorDomain x, ‖remainderSeries x α‖ ^ 2) := hle
    _ ≤ starNorm x 0 * (∫ α in Set.Ioc (0 : ℝ) 1, ‖remainderSeries x α‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
    _ = _ := by
      simp_rw [remainderSeries_eq_charSeries hx]
      rw [charSeries_parseval _ (remainderCoeff_summable hx)]

end LeanLab.Ternary.Task580

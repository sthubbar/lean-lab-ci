/-
P0028, https://arxiv.org/abs/1610.02017, section 4.3, page 9.
Weighted Holder bookkeeping for three factors on the unit interval.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
open MeasureTheory Finset
open scoped ENNReal
namespace LeanLab.Ternary.MMS

/-- The weighted three factor Holder inequality on the unit interval. -/
theorem intervalIntegral_prod_rpow_le (F : Fin 3 → ℝ → ℝ)
    (hF : ∀ i, Continuous (F i)) (hF0 : ∀ i x, 0 ≤ F i x)
    (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (hw0 : ∀ i, 0 ≤ w i) :
    (∫ x in (0 : ℝ)..1, ∏ i, F i x ^ w i) ≤
      ∏ i, (∫ x in (0 : ℝ)..1, F i x) ^ w i := by
  let μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hi (i : Fin 3) : Integrable (F i) μ := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      ((hF i).intervalIntegrable 0 1)
  have hh := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (univ : Finset (Fin 3))
    (f := fun i x => ENNReal.ofReal (F i x))
    (fun i _ => ((hF i).measurable.ennreal_ofReal.aemeasurable)) hw (fun i _ => hw0 i)
  have hfin (i : Fin 3) : (∫⁻ x, ENNReal.ofReal (F i x) ∂μ) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (Filter.Eventually.of_forall (hF0 i))]
    exact ENNReal.ofReal_ne_top
  have hRfin : (∏ i, (∫⁻ x, ENNReal.ofReal (F i x) ∂μ) ^ w i) ≠ ⊤ := by
    apply ENNReal.prod_ne_top
    intro i _
    exact ENNReal.rpow_ne_top_of_nonneg (hw0 i) (hfin i)
  have hh' := ENNReal.toReal_mono hRfin hh
  have hleft : (∫ x, ∏ i, F i x ^ w i ∂μ) =
      (∫⁻ x, ∏ i, ENNReal.ofReal (F i x) ^ w i ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_prod_of_nonneg]
      · apply prod_congr rfl
        intro i _
        exact (ENNReal.ofReal_rpow_of_nonneg (hF0 i x) (hw0 i)).symm
      · intro i _
        exact Real.rpow_nonneg (hF0 i x) _
    · exact Filter.Eventually.of_forall (fun x => prod_nonneg (fun i _ => Real.rpow_nonneg (hF0 i x) _))
    · apply Continuous.aestronglyMeasurable
      apply continuous_finsetProd
      intro i _
      exact (hF i).rpow_const (fun x => Or.inr (hw0 i))
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ x, ∏ i, F i x ^ w i ∂μ) ≤ ∏ i, (∫ x, F i x ∂μ) ^ w i
  rw [hleft]
  convert hh' using 1
  rw [ENNReal.toReal_prod]
  apply prod_congr rfl
  intro i _
  rw [← ENNReal.toReal_rpow, ← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (hF0 i)) (hi i).aestronglyMeasurable]
end LeanLab.Ternary.MMS

namespace LeanLab.Ternary.MMS
open MeasureTheory Finset
open scoped ENNReal

/-- Interpolating one uniform factor gives the three factor restriction bound. -/
theorem integral_three_uniform_bound (A B C : ℝ → ℝ)
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 ≤ B x) (hC0 : ∀ x, 0 ≤ C x)
    {q M : ℝ} (hq : 2 < q) (hq3 : q < 3) (hAM : ∀ x, A x ≤ M) :
    (∫ x in (0 : ℝ)..1, A x * B x * C x) ≤
      M ^ (3 - q) * (∫ x in (0 : ℝ)..1, A x ^ q) ^ ((q - 2) / q) *
        (∫ x in (0 : ℝ)..1, B x ^ q) ^ (1 / q) *
        (∫ x in (0 : ℝ)..1, C x ^ q) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  let F : Fin 3 → ℝ → ℝ := ![fun x => A x ^ q, fun x => B x ^ q, fun x => C x ^ q]
  let w : Fin 3 → ℝ := ![(q - 2) / q, 1 / q, 1 / q]
  have hF : ∀ i, Continuous (F i) := by
    intro i
    fin_cases i
    · exact hA.rpow_const (fun _ => Or.inr hq0.le)
    · exact hB.rpow_const (fun _ => Or.inr hq0.le)
    · exact hC.rpow_const (fun _ => Or.inr hq0.le)
  have hF0 : ∀ i x, 0 ≤ F i x := by
    intro i x
    fin_cases i
    · exact Real.rpow_nonneg (hA0 x) _
    · exact Real.rpow_nonneg (hB0 x) _
    · exact Real.rpow_nonneg (hC0 x) _
  have hw : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_succ]
    field_simp
    <;> ring
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i <;> dsimp [w] <;> positivity
  have H := intervalIntegral_prod_rpow_le F hF hF0 w hw hw0
  have hqp : q * ((q - 2) / q) = q - 2 := by field_simp
  have hqi : q * (1 / q) = 1 := by field_simp
  have hprod (x : ℝ) : (∏ i, F i x ^ w i) = A x ^ (q - 2) * B x * C x := by
    simp only [F, w, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, mul_one]
    rw [← Real.rpow_mul (hA0 x), ← Real.rpow_mul (hB0 x), ← Real.rpow_mul (hC0 x),
      hqp, hqi, Real.rpow_one, Real.rpow_one]
    ring
  have hR : (∏ i, (∫ x in (0 : ℝ)..1, F i x) ^ w i) =
      (∫ x in (0 : ℝ)..1, A x ^ q) ^ ((q - 2) / q) *
        (∫ x in (0 : ℝ)..1, B x ^ q) ^ (1 / q) *
        (∫ x in (0 : ℝ)..1, C x ^ q) ^ (1 / q) := by
    simp [F, w, Fin.prod_univ_succ, mul_assoc]
  simp_rw [hprod] at H
  rw [hR] at H
  have hpoint (x : ℝ) : A x * B x * C x ≤
      M ^ (3 - q) * (A x ^ (q - 2) * B x * C x) := by
    have he : A x = A x ^ (3 - q) * A x ^ (q - 2) := by
      rw [← Real.rpow_add' (hA0 x) (by linarith : (3 - q) + (q - 2) ≠ 0)]
      norm_num
    calc A x * B x * C x = A x ^ (3 - q) * (A x ^ (q - 2) * B x * C x) := by
          conv_lhs => rw [he]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hA0 x) (hAM x) (by linarith))
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg (hA0 x) _) (hB0 x)) (hC0 x))
  have hcont : Continuous (fun x => A x ^ (q - 2) * B x * C x) :=
    ((hA.rpow_const (fun _ => Or.inr (by linarith))).mul hB).mul hC
  calc (∫ x in (0 : ℝ)..1, A x * B x * C x)
      ≤ ∫ x in (0 : ℝ)..1, M ^ (3 - q) * (A x ^ (q - 2) * B x * C x) :=
        intervalIntegral.integral_mono (by norm_num)
          ((hA.mul hB |>.mul hC).intervalIntegrable 0 1)
          ((continuous_const.mul hcont).intervalIntegrable 0 1) hpoint
    _ = M ^ (3 - q) * ∫ x in (0 : ℝ)..1, A x ^ (q - 2) * B x * C x :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      have hm : 0 ≤ M := (hA0 0).trans (hAM 0)
      have h := mul_le_mul_of_nonneg_left H (Real.rpow_nonneg hm (3 - q))
      simpa only [mul_assoc] using h
end LeanLab.Ternary.MMS

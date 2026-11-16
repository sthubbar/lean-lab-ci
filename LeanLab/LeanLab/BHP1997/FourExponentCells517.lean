/-
P0069, Section 5, page 51, display 5.17.
The smooth cell estimates used in the E4 exponent quadrature.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentMesh517
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.PSeries

namespace LeanLab.BHP1997.LowerShortC165
open MeasureTheory

/-- Page 51 display 5.17. A rectangle rule with a perturbed cell weight.
The first error is the weight discrepancy. The second is the Lipschitz error. -/
theorem four_exponent_cell_quadrature (f : ℝ → ℝ) {a b w M K : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hi : IntervalIntegrable f volume a b) (hf : |f a| ≤ M)
    (hlip : ∀ t ∈ Set.Icc a b, |f a - f t| ≤ K * |t - a|) :
    |w * f a - ∫ t in a..b, f t| ≤ M * |w - (b-a)| + K * (b-a)^2 := by
  have heq : (∫ t in a..b, f a - f t) = (b-a) * f a - ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const, smul_eq_mul]
  have hbound : |(b-a) * f a - ∫ t in a..b, f t| ≤ K * (b-a)^2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => f a - f t) (C := K * (b-a)) (fun t ht => by
        rw [Set.uIoc_of_le hab] at ht
        rw [Real.norm_eq_abs]
        refine (hlip t ⟨ht.1.le, ht.2⟩).trans ?_
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hK)
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hb
    nlinarith
  have he : w * f a - ∫ t in a..b, f t =
      (w-(b-a)) * f a + ((b-a) * f a - ∫ t in a..b, f t) := by ring
  rw [he]
  calc _ ≤ |(w-(b-a)) * f a| + |(b-a) * f a - ∫ t in a..b, f t| := abs_add_le _ _
    _ ≤ M * |w-(b-a)| + K * (b-a)^2 := by
      rw [abs_mul, mul_comm |w-(b-a)|]
      exact add_le_add (mul_le_mul_of_nonneg_right hf (abs_nonneg _)) hbound

/-- Page 51 display 5.17. On a smooth logarithmic cell the rectangle error is
at most M over n squared log Z plus K over n squared log Z squared. -/
theorem four_exponent_log_cell_error (f : ℝ → ℝ) {Z n M K : ℝ}
    (hZ : 1 < Z) (hn : 0 < n) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hi : IntervalIntegrable f volume (Real.log n / Real.log Z)
      (Real.log (n+1) / Real.log Z))
    (hf : |f (Real.log n / Real.log Z)| ≤ M)
    (hlip : ∀ t ∈ Set.Icc (Real.log n / Real.log Z) (Real.log (n+1) / Real.log Z),
      |f (Real.log n / Real.log Z) - f t| ≤ K * |t - Real.log n / Real.log Z|) :
    |f (Real.log n / Real.log Z) / (n * Real.log Z) -
        ∫ t in (Real.log n / Real.log Z)..(Real.log (n+1) / Real.log Z), f t| ≤
      M / (n^2 * Real.log Z) + K / (n^2 * Real.log Z ^ 2) := by
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have hw : 0 ≤ 1 / (n * Real.log Z) := by positivity
  obtain ⟨hlo, hhi⟩ := four_exponent_mesh_bounds hZ hn
  obtain ⟨he0, he⟩ := four_exponent_mesh_error hZ hn
  have hd : 0 ≤ Real.log (n+1) / Real.log Z - Real.log n / Real.log Z :=
    (by positivity : (0 : ℝ) ≤ 1 / ((n+1) * Real.log Z)).trans hlo
  have hb := four_exponent_cell_quadrature f (w := 1 / (n * Real.log Z))
    (sub_nonneg.mp hd) hM hK hi hf hlip
  rw [one_div_mul_eq_div] at hb
  refine hb.trans ?_
  rw [abs_of_nonneg he0]
  have hs : (Real.log (n+1) / Real.log Z - Real.log n / Real.log Z)^2 ≤
      (1 / (n * Real.log Z))^2 := by nlinarith
  calc _ ≤ M * (1 / (n^2 * Real.log Z)) + K * (1 / (n * Real.log Z))^2 :=
        add_le_add (mul_le_mul_of_nonneg_left he hM) (mul_le_mul_of_nonneg_left hs hK)
    _ = _ := by ring

/-- Page 51 display 5.17. The smooth cell errors sum to a power saving at
the lower index cutoff. Mathlib supplies the reciprocal square tail bound. -/
theorem four_exponent_cell_errors_sum (r : ℕ → ℝ) {L N : ℕ}
    (hL : 1 ≤ L) (hLN : L ≤ N) {Z M K : ℝ}
    (hZ : 1 < Z) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hr : ∀ n ∈ Finset.Ioc L N, |r n| ≤
      M / ((n : ℝ)^2 * Real.log Z) + K / ((n : ℝ)^2 * Real.log Z ^ 2)) :
    |∑ n ∈ Finset.Ioc L N, r n| ≤
      (M / Real.log Z + K / Real.log Z ^ 2) / L := by
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hc : 0 ≤ M / Real.log Z + K / Real.log Z ^ 2 := by positivity
  have hs : (∑ n ∈ Finset.Ioc L N, ((n : ℝ)^2)⁻¹) ≤ (L : ℝ)⁻¹ :=
    (sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : L ≠ 0) hLN).trans
      (sub_le_self _ (by positivity))
  calc _ ≤ ∑ n ∈ Finset.Ioc L N, |r n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ioc L N,
        (M / Real.log Z + K / Real.log Z ^ 2) * ((n : ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      convert hr n hn using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
    _ = (M / Real.log Z + K / Real.log Z ^ 2) *
        (∑ n ∈ Finset.Ioc L N, ((n : ℝ)^2)⁻¹) := (Finset.mul_sum _ _ _).symm
    _ ≤ (M / Real.log Z + K / Real.log Z ^ 2) * (L : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hs hc
    _ = _ := rfl

#print axioms four_exponent_cell_quadrature
#print axioms four_exponent_log_cell_error
#print axioms four_exponent_cell_errors_sum
end LeanLab.BHP1997.LowerShortC165

/-
Elementary normalization tools for P0069 Baker Harman Pintz 1997, pages 43 and 52.
These are lab auxiliary statements. The raw coefficient mean squares remain inputs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Abel514
namespace LeanLab.BHP1997.Task670WeightedMeanSquare
open MeasureTheory
open scoped BigOperators
/-- Weighted finite Cauchy Schwarz for the normalization audit of P0069 pages 43 and 52. -/
theorem finite_weighted_square {ι : Type*} (s : Finset ι) (c v : ι → ℂ) :
    ‖∑ i ∈ s, c i * v i‖ ^ 2 ≤
      (∑ i ∈ s, ‖c i‖) * ∑ i ∈ s, ‖c i‖ * ‖v i‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i _ => norm_nonneg (c i)) (fun i _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  intro i _
  rw [norm_mul]
  exact le_of_eq (by ring)
/-- A finite linear combination of continuous functions inherits uniform weighted mean squares.
The loss is the square of the sum of the coefficient norms. P0069 page 43 displays 5.1 and 5.2
and page 52 use this elementary transfer for the lab normalization. -/
theorem finite_weighted_mean_square {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℝ → ℂ)
    (w : ℝ → ℝ) {a b R : ℝ} (hab : a ≤ b)
    (hf : ∀ i ∈ s, Continuous (f i)) (hw : Continuous w)
    (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t)
    (hR : ∀ i ∈ s, (∫ t in a..b, ‖f i t‖ ^ 2 * w t) ≤ R) :
    (∫ t in a..b, ‖∑ i ∈ s, c i * f i t‖ ^ 2 * w t) ≤
      (∑ i ∈ s, ‖c i‖) ^ 2 * R := by
  let P : ℝ := ∑ i ∈ s, ‖c i‖
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hsum : Continuous (fun t => ∑ i ∈ s, c i * f i t) :=
    continuous_finsetSum _ fun i hi => continuous_const.mul (hf i hi)
  have henergy : ∀ i ∈ s, Continuous (fun t => ‖f i t‖ ^ 2 * w t) :=
    fun i hi => ((hf i hi).norm.pow 2).mul hw
  have hmajor : Continuous (fun t => P * ∑ i ∈ s, ‖c i‖ * (‖f i t‖ ^ 2 * w t)) :=
    continuous_const.mul (continuous_finsetSum _ fun i hi => continuous_const.mul (henergy i hi))
  have hpoint (t : ℝ) : ‖∑ i ∈ s, c i * f i t‖ ^ 2 ≤
      P * ∑ i ∈ s, ‖c i‖ * ‖f i t‖ ^ 2 := finite_weighted_square s c (fun i => f i t)
  calc
    _ ≤ ∫ t in a..b, P * ∑ i ∈ s, ‖c i‖ * (‖f i t‖ ^ 2 * w t) := by
      apply intervalIntegral.integral_mono_on hab
        (((hsum.norm.pow 2).mul hw).intervalIntegrable a b) (hmajor.intervalIntegrable a b)
      intro t ht
      have hh := mul_le_mul_of_nonneg_right (hpoint t) (hw0 t ht)
      simpa only [Finset.sum_mul, mul_assoc, Pi.mul_apply, Pi.pow_apply] using hh
    _ = P * ∑ i ∈ s, ‖c i‖ * (∫ t in a..b, ‖f i t‖ ^ 2 * w t) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul]
      · intro i hi; exact (continuous_const.mul (henergy i hi)).intervalIntegrable _ _
    _ ≤ P * ∑ i ∈ s, ‖c i‖ * R := by
      apply mul_le_mul_of_nonneg_left _ hP
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hR i hi) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; dsimp [P]; ring

/-- Discrete partial summation transfers weighted mean squares from every prefix to a
coefficient multiplier. The loss is endpoint norm plus total variation, squared.
This is the elementary normalization step for P0069 page 43 displays 5.1 and 5.2. -/
theorem abel_weighted_mean_square (s : Finset ℕ) {L U : ℕ} (hLU : L ≤ U)
    (hs : ∀ m ∈ s, L ≤ m ∧ m ≤ U) (F : ℕ → ℂ) (a : ℕ → ℝ → ℂ)
    (w : ℝ → ℝ) {u v R : ℝ} (huv : u ≤ v)
    (ha : ∀ m ∈ s, Continuous (a m)) (hw : Continuous w)
    (hw0 : ∀ t ∈ Set.Icc u v, 0 ≤ w t)
    (hprefix : ∀ i ∈ Finset.Icc L U,
      (∫ t in u..v, ‖∑ m ∈ s.filter (fun m => m ≤ i), a m t‖ ^ 2 * w t) ≤ R) :
    (∫ t in u..v, ‖∑ m ∈ s, F m * a m t‖ ^ 2 * w t) ≤
      (‖F U‖ + ∑ i ∈ Finset.Ico L U, ‖F (i + 1) - F i‖) ^ 2 * R := by
  classical
  let c : ℕ → ℂ := fun i => if i = U then F U else -(F (i + 1) - F i)
  let P : ℕ → ℝ → ℂ := fun i t => ∑ m ∈ s.filter (fun m => m ≤ i), a m t
  have htop : s.filter (fun m => m ≤ U) = s :=
    Finset.filter_eq_self.mpr fun m hm => (hs m hm).2
  have hrep (t : ℝ) : (∑ m ∈ s, F m * a m t) = ∑ i ∈ Finset.Icc L U, c i * P i t := by
    rw [← Finset.sum_Ico_add_eq_sum_Icc hLU]
    have hsum : (∑ i ∈ Finset.Ico L U, c i * P i t) =
        -(∑ i ∈ Finset.Ico L U, (F (i + 1) - F i) * P i t) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiU : i ≠ U := ne_of_lt (Finset.mem_Ico.mp hi).2
      simp only [c, ite_eq_right hiU, neg_mul]
    rw [hsum]
    simp only [c, ite_true, P, htop]
    rw [Decomp514Abel.finite_abel s hs F (fun m => a m t)]
    ring
  have hc : (∑ i ∈ Finset.Icc L U, ‖c i‖) =
      ‖F U‖ + ∑ i ∈ Finset.Ico L U, ‖F (i + 1) - F i‖ := by
    rw [← Finset.sum_Ico_add_eq_sum_Icc hLU]
    have hsum : (∑ i ∈ Finset.Ico L U, ‖c i‖) =
        ∑ i ∈ Finset.Ico L U, ‖F (i + 1) - F i‖ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiU : i ≠ U := ne_of_lt (Finset.mem_Ico.mp hi).2
      simp only [c, ite_eq_right hiU, norm_neg]
    rw [hsum]
    simp only [c, ite_true]
    ring
  have hPc : ∀ i ∈ Finset.Icc L U, Continuous (P i) := by
    intro i _
    exact continuous_finsetSum _ fun m hm => ha m (Finset.mem_filter.mp hm).1
  simp_rw [hrep]
  have h := finite_weighted_mean_square (Finset.Icc L U) c P w huv hPc hw hw0 hprefix
  rwa [hc] at h

end LeanLab.BHP1997.Task670WeightedMeanSquare

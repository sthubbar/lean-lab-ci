/-
AI wrote this Lean code for CODEX task58.
A tight bound for the actual IB1 integral in the lab model of P0039 equation 3.9.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58MassIntegral
import LeanLab.ChenPrimeExceptional.U1435C0

open Real Finset intervalIntegral MeasureTheory Set

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- Exact algebra for the change of variable in the density. -/
theorem density_transform {t : ℝ} (ht : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 3)) :
    density t = 3 * massKernel (-3 * t + 1) := by
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
  unfold density massKernel reciprocalKernel
  have he : (1 : ℝ) + (-3 * t + 1) = 2 - 3 * t := by ring
  rw [he]
  have h1 : 1 - (-3 * t + 1) = 3 * t := by ring
  have h2 : 2 + (-3 * t + 1) = 3 * (1 - t) := by ring
  rw [h1, h2]
  field_simp
  <;> ring

/-- The original IB1 integral equals the transformed kernel integral. -/
theorem IB1_transform : U1435.IB1 = ∫ q in (0 : ℝ)..(7 / 10), massKernel q := by
  unfold U1435.IB1
  change (∫ t in (1 / 10 : ℝ)..(1 / 3), density t) = _
  rw [integral_congr (fun t ht => density_transform (by
    rw [uIcc_of_le (show (1 / 10 : ℝ) ≤ 1 / 3 by norm_num)] at ht
    exact ht))]
  rw [intervalIntegral.integral_const_mul, integral_comp_mul_add massKernel (by norm_num : (-3 : ℝ) ≠ 0) 1]
  norm_num
  rw [integral_symm]
  ring

/-- The product polynomial is continuous everywhere. -/
theorem massPoly_continuous : Continuous massPoly := by
  have h : Continuous (fun q : ℝ => ∑ i ∈ range 60, ∑ j ∈ range 70,
      (-(-1 : ℝ) ^ (i + 1) / (i + 1) * (1 + (-1 / 2 : ℝ) ^ j / 2)) *
        q ^ (i + j + 1)) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
      continuous_const.mul (continuous_id.pow _)))
  convert h using 1
  ext q
  exact massPoly_expansion q

/-- The transformed actual kernel is continuous on the integration interval. -/
theorem massKernel_continuous : ContinuousOn massKernel (Set.Icc (0 : ℝ) (7 / 10)) := by
  apply ContinuousOn.mul
  · exact (continuousOn_const.add continuousOn_id).log (by
      intro q hq
      change 1 + q ≠ 0
      linarith [hq.1])
  · apply ContinuousOn.add
    · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id) (by
        intro q hq
        change 1 - q ≠ 0
        linarith [hq.2])
    · exact continuousOn_const.div (continuousOn_const.add continuousOn_id) (by
        intro q hq
        change 2 + q ≠ 0
        linarith [hq.1])

/-- The polynomial mass approximates the original IB1 integral within seven billionths. -/
theorem IB1_polynomial_error :
    |U1435.IB1 - (polynomialMassQ : ℝ)| ≤ (7 / 1000000000 : ℝ) := by
  have hp : IntervalIntegrable massPoly volume (0 : ℝ) (7 / 10) :=
    massPoly_continuous.intervalIntegrable _ _
  have hk : IntervalIntegrable massKernel volume (0 : ℝ) (7 / 10) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (show (0 : ℝ) ≤ 7 / 10 by norm_num)]
    exact massKernel_continuous
  have h := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (7 / 10 : ℝ))
      (C := (1 / 100000000 : ℝ)) (f := fun q => massPoly q - massKernel q) (by
        intro q hq
        rw [uIoc_of_le (show (0 : ℝ) ≤ 7 / 10 by norm_num)] at hq
        rw [Real.norm_eq_abs]
        exact massPoly_error ⟨hq.1.le, hq.2⟩)
  rw [integral_sub hp hk, integral_massPoly, ← IB1_transform, Real.norm_eq_abs] at h
  rw [abs_sub_comm]
  convert h using 1 <;> norm_num

/-- The actual IB1 integral satisfies its original tight box without any numerical input. -/
theorem IB1_bracket_unconditional : (0.490995 : ℝ) ≤ U1435.IB1 ∧ U1435.IB1 ≤ 0.490996 := by
  have hl : (0.49099519 : ℝ) ≤ (polynomialMassQ : ℝ) := by
    have h : ((0.49099519 : ℚ) : ℝ) ≤ (polynomialMassQ : ℝ) :=
      Rat.cast_le.mpr polynomialMassQ_bounds.1
    norm_num at h ⊢
    exact h
  have hu : (polynomialMassQ : ℝ) ≤ (0.49099522 : ℝ) := by
    have h : (polynomialMassQ : ℝ) ≤ ((0.49099522 : ℚ) : ℝ) :=
      Rat.cast_le.mpr polynomialMassQ_bounds.2
    norm_num at h ⊢
    exact h
  have he := IB1_polynomial_error
  rw [abs_le] at he
  constructor <;> linarith

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.density_transform
#print axioms LeanLab.ChenPrimeExceptional.Task58.IB1_transform
#print axioms LeanLab.ChenPrimeExceptional.Task58.massPoly_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.massKernel_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.IB1_polynomial_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.IB1_bracket_unconditional

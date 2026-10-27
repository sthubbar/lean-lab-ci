/-
P0059 arXiv 1407.7902v1 page 10, Lemma 3.1 second line.
Journal INTEGERS 14 A61 page 13 equation 68.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.WeightDerivative
import LeanLab.KadiriLumley2014.WeightMass

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- The normalized first derivative factor from equation 2.21. -/
noncomputable def firstFactor (m : ℕ) (δ : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ 2 * |weightD m t|) /
    (∫ t in (0 : ℝ)..1, weight m t)

/-- Unnormalized first factor bounds before substituting the factorial mass. -/
theorem first_factor_numerator_bounds {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) :
    2 ≤ (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ 2 * |weightD m t|) ∧
    (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ 2 * |weightD m t|) ≤ 2 * (1 + δ) ^ 2 := by
  have hi : IntervalIntegrable (fun t => |weightD m t|) volume 0 1 :=
    (weightD_continuous m).abs.intervalIntegrable _ _
  have hj : IntervalIntegrable (fun t => (1 + δ * t) ^ 2 * |weightD m t|) volume 0 1 :=
    (by unfold weightD; fun_prop : Continuous (fun t : ℝ => (1 + δ * t) ^ 2 * |weightD m t|)).intervalIntegrable _ _
  constructor
  · rw [← weightD_abs_integral hm]
    apply intervalIntegral.integral_mono_on (by norm_num) hi hj
    intro t ht
    have h1 : 1 ≤ 1 + δ * t := by nlinarith [ht.1]
    have hs : 1 ≤ (1 + δ * t) ^ 2 := by nlinarith
    nlinarith [abs_nonneg (weightD m t)]
  · have hc : IntervalIntegrable (fun t => (1 + δ) ^ 2 * |weightD m t|) volume 0 1 :=
      hi.const_mul _
    have hmono : (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ 2 * |weightD m t|) ≤
        ∫ t in (0 : ℝ)..1, (1 + δ) ^ 2 * |weightD m t| := by
      apply intervalIntegral.integral_mono_on (by norm_num) hj hc
      intro t ht
      have h0 : 0 ≤ 1 + δ * t := by nlinarith [ht.1]
      have h1 : 1 + δ * t ≤ 1 + δ := by nlinarith [ht.2]
      have hs : (1 + δ * t) ^ 2 ≤ (1 + δ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    simpa [intervalIntegral.integral_const_mul, weightD_abs_integral hm, mul_comm] using hmono

/-- Lemma 3.1 first derivative bounds expressed using the positive mass. -/
theorem first_factor_bounds_mass {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) :
    2 / (∫ t in (0 : ℝ)..1, weight m t) ≤ firstFactor m δ ∧
    firstFactor m δ ≤ 2 * (1 + δ) ^ 2 / (∫ t in (0 : ℝ)..1, weight m t) := by
  obtain ⟨hl, hu⟩ := first_factor_numerator_bounds hm hδ
  exact ⟨(div_le_div_iff_of_pos_right (weight_mass_pos m)).mpr hl,
    (div_le_div_iff_of_pos_right (weight_mass_pos m)).mpr hu⟩

/-- The factorial ratio lambda zero from Lemma 3.1. -/
noncomputable def lambdaZero (m : ℕ) : ℝ :=
  (2 * m + 1).factorial / (2 ^ (2 * m - 1) * (m.factorial : ℝ) ^ 2)

/-- The first derivative norm divided by mass equals the printed lambda zero. -/
theorem two_div_mass_eq_lambdaZero {m : ℕ} (hm : 0 < m) :
    2 / (∫ t in (0 : ℝ)..1, weight m t) = lambdaZero m := by
  rw [weight_mass]
  have he : 2 * m = (2 * m - 1) + 1 := by omega
  have hp : (2 : ℝ) ^ (2 * m) = 2 ^ (2 * m - 1) * 2 := by
    conv_lhs => rw [he]
    rw [pow_succ]
  unfold lambdaZero
  rw [hp]
  field_simp

/-- Lemma 3.1 second line with the paper's factorial ratios. -/
theorem first_factor_bounds {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) :
    lambdaZero m ≤ firstFactor m δ ∧
    firstFactor m δ ≤ (1 + δ) ^ 2 * lambdaZero m := by
  obtain ⟨hl, hu⟩ := first_factor_bounds_mass hm hδ
  rw [two_div_mass_eq_lambdaZero hm] at hl
  refine ⟨hl, hu.trans_eq ?_⟩
  rw [← two_div_mass_eq_lambdaZero hm]
  ring

end LeanLab.KadiriLumley2014.Task64

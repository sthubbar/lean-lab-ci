/-
Weighted Cauchy Schwarz for P0079 page 9, the individual replacement estimates.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.MajorErrors418

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, the Cauchy Schwarz step in the J2 and J3 estimates.
Two explicit second-moment bounds and a bounded continuous weight control the product integral. -/
theorem weighted_major_product418 (f g h : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (X A a b W : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hb : 0 < b)
    (hH : ∀ α ∈ major293 X, ‖h α‖ ≤ A)
    (hF : (∫ α in major293 X, ‖f α‖ ^ 2) ≤ a ^ 2 * W)
    (hG : (∫ α in major293 X, ‖g α‖ ^ 2) ≤ b ^ 2 * W) :
    ‖∫ α in major293 X, f α * g α * h α‖ ≤ A * a * b * W := by
  have hset : major293 X = Set.Icc (-(X ^ (1 / 3 : ℝ) / X)) (X ^ (1 / 3 : ℝ) / X) := by
    ext α
    change |α| ≤ X ^ (1 / 3 : ℝ) / X ↔ _
    exact abs_le
  have hiF : IntegrableOn (fun α => ‖f α‖ ^ 2) (major293 X) := by
    rw [hset]
    exact (hf.norm.pow 2).integrableOn_Icc
  have hiG : IntegrableOn (fun α => ‖g α‖ ^ 2) (major293 X) := by
    rw [hset]
    exact (hg.norm.pow 2).integrableOn_Icc
  have hp : ∀ α ∈ major293 X,
      ‖f α * g α * h α‖ ≤ A / 2 * ((b / a) * ‖f α‖ ^ 2 + (a / b) * ‖g α‖ ^ 2) := by
    intro α hα
    have he : ((b / a) * ‖f α‖ ^ 2 + (a / b) * ‖g α‖ ^ 2) / 2 - ‖f α‖ * ‖g α‖ =
        (b * ‖f α‖ - a * ‖g α‖) ^ 2 / (2 * a * b) := by field_simp; ring
    have hy : ‖f α‖ * ‖g α‖ ≤
        ((b / a) * ‖f α‖ ^ 2 + (a / b) * ‖g α‖ ^ 2) / 2 := by
      have H := div_nonneg (sq_nonneg (b * ‖f α‖ - a * ‖g α‖))
        (by positivity : 0 ≤ 2 * a * b)
      linarith only [he, H]
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (‖f α‖ * ‖g α‖) * A := mul_le_mul_of_nonneg_left (hH α hα) (by positivity)
      _ ≤ (((b / a) * ‖f α‖ ^ 2 + (a / b) * ‖g α‖ ^ 2) / 2) * A :=
        mul_le_mul_of_nonneg_right hy hA
      _ = _ := by ring
  calc
    _ ≤ ∫ α in major293 X, ‖f α * g α * h α‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ α in major293 X, A / 2 * ((b / a) * ‖f α‖ ^ 2 + (a / b) * ‖g α‖ ^ 2) := by
      apply setIntegral_mono_on
        (continuous_major_integrable418 _ ((hf.mul hg).mul hh) X).norm
        (((hiF.const_mul _).add (hiG.const_mul _)).const_mul _)
        (by rw [hset]; exact measurableSet_Icc)
      exact hp
    _ = A / 2 * ((b / a) * (∫ α in major293 X, ‖f α‖ ^ 2) +
        (a / b) * (∫ α in major293 X, ‖g α‖ ^ 2)) := by
      rw [integral_const_mul, integral_add (hiF.const_mul _) (hiG.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ A / 2 * ((b / a) * (a ^ 2 * W) + (a / b) * (b ^ 2 * W)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hF (by positivity))
        (mul_le_mul_of_nonneg_left hG (by positivity))) (by positivity)
    _ = _ := by field_simp; ring

end LeanLab.LZPowersOfTwo

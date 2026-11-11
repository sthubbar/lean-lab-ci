import LeanLab.ExceptionalSet.Localization446

/-!
P0082 page369 display39, the translated strip geometry.
The centre can be any real translate, including the printed half integers.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Decomp483e
open Real MeasureTheory Set

/-- P0082 page369 display39, derived explicit strip bound. A strip
centred at x plus d has length twice r. Uniform inner bounds leave the outer mass. -/
theorem translated_strip_integral_le (A : Set ℝ) (g : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (hg : IntegrableOn g A) (hg0 : ∀ x, 0 ≤ g x) (hH0 : ∀ x y, 0 ≤ H x y)
    (d r B T : ℝ) (hr : 0 ≤ r) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hgb : ∀ x ∈ A, g x ≤ B) (hH : ∀ x ∈ A, ∀ y ∈ A, H x y ≤ T) :
    (∫ x in A, ∫ y in A ∩ {y : ℝ | |y - x - d| ≤ r}, g x * g y * H x y) ≤
      2 * r * B * T * (∫ x in A, g x) := by
  have hi (x : ℝ) (hx : x ∈ A) :
      (∫ y in A ∩ {y : ℝ | |y - x - d| ≤ r}, g x * g y * H x y) ≤
        (2 * r * B * T) * g x := by
    have hsub : A ∩ {y : ℝ | |y - x - d| ≤ r} ⊆ Icc (x + d - r) (x + d + r) := by
      intro y hy
      have hh := abs_le.mp (show |y - x - d| ≤ r from hy.2)
      constructor <;> linarith
    have hconst : IntegrableOn (fun _ : ℝ => g x * B * T) (Icc (x + d - r) (x + d + r)) :=
      integrableOn_const (by simp)
    calc
      _ ≤ ∫ y in A ∩ {y : ℝ | |y - x - d| ≤ r}, g x * B * T := by
        apply setIntegral_mono_of_nonneg
        · intro y hy
          exact mul_nonneg (mul_nonneg (hg0 x) (hg0 y)) (hH0 x y)
        · intro y hy
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hgb y hy.1) (hg0 x))
            (hH x hx y hy.1) (hH0 x y) (mul_nonneg (hg0 x) hB)
        · exact hconst.mono_set hsub
      _ ≤ ∫ y in Icc (x + d - r) (x + d + r), g x * B * T :=
        setIntegral_mono_set hconst
          (Filter.Eventually.of_forall (fun _ => mul_nonneg (mul_nonneg (hg0 x) hB) hT))
          hsub.eventuallySubset
      _ = _ := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ x + d + r - (x + d - r))]
        ring
  calc
    _ ≤ ∫ x in A, (2 * r * B * T) * g x := by
      apply setIntegral_mono_of_nonneg
      · intro x hx
        apply integral_nonneg
        intro y
        exact mul_nonneg (mul_nonneg (hg0 x) (hg0 y)) (hH0 x y)
      · exact hi
      · exact hg.const_mul _
    _ = _ := integral_const_mul _ _

end LeanLab.ExceptionalSet.Decomp483e

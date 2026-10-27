/-
P0028, arXiv 1610.02017, Lemma 4.3 item 1, page 10.
Elementary positivity and monotonicity of the double average.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrSmoothing

namespace LeanLab.Ternary.MMS
open Finset

/-- Smoothing a nonnegative function stays nonnegative. -/
theorem intSmooth_nonneg (B : Finset ℤ) (f : ℤ →₀ ℝ)
    (hf : ∀ n, 0 ≤ f n) (n : ℤ) : 0 ≤ intSmooth B f n := by
  rw [intSmooth_apply]
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro a ha
  apply sum_nonneg
  intro b hb
  exact hf _

/-- The double average preserves pointwise majorization. -/
theorem intSmooth_mono (B : Finset ℤ) (f g : ℤ →₀ ℝ)
    (hfg : ∀ n, f n ≤ g n) (n : ℤ) : intSmooth B f n ≤ intSmooth B g n := by
  rw [intSmooth_apply, intSmooth_apply]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  exact hfg _

/-- A nonempty double average preserves a constant pointwise upper bound. -/
theorem intSmooth_le_const (B : Finset ℤ) (hB : B.Nonempty) (f : ℤ →₀ ℝ)
    (U : ℝ) (hf : ∀ n, f n ≤ U) (n : ℤ) : intSmooth B f n ≤ U := by
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  rw [intSmooth_apply]
  have hsum : (∑ a ∈ B, ∑ b ∈ B, f (n + a - b)) ≤ ∑ a ∈ B, ∑ b ∈ B, U := by
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro b hb
    exact hf _
  calc (1 / (B.card : ℝ) ^ 2) * (∑ a ∈ B, ∑ b ∈ B, f (n + a - b))
      ≤ (1 / (B.card : ℝ) ^ 2) * (∑ a ∈ B, ∑ b ∈ B, U) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = U := by
      simp only [sum_const, nsmul_eq_mul]
      field_simp

end LeanLab.Ternary.MMS

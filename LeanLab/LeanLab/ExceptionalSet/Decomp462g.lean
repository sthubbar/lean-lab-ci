import LeanLab.ExceptionalSet.Decomp462f

/-!
Exact elementary companions for the remaining fold and scalar splits.
Source: https://doi.org/10.5802/aif.1621, pages 356 and 359.
The full generic fold is already proved. These supplies expose its elementary steps.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462g

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC)
/-- P0082 page 356, auxiliary proof step. The integer period removes the translate from h. -/
theorem periodic_translate_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v α : ℝ) (n : ℤ) :
    h (α + n) * K (α + n) * eC (-((α + n) * v)) =
      h α * (K (α + n) * eC (-((α + n) * v))) := by
  rw [show h (α + n) = h α by simpa only [mul_one] using hper.int_mul n α, mul_assoc]
/-- P0082 page 356, auxiliary proof step. Change variables in one translated unit interval. -/
theorem translate_interval_supplied (f : ℝ → ℂ) (n : ℤ) :
    (∫ α in (n : ℝ)..((n : ℝ) + 1), f α) = ∫ α in (0 : ℝ)..1, f (α + n) := by
  rw [intervalIntegral.integral_comp_add_right]
  simp [add_comm]
/-- P0082 page 356, auxiliary proof step. Partition the integrable real line into integer unit intervals. -/
theorem partition_supplied (f : ℝ → ℂ) (hf : Integrable f) :
    (∫ α, f α) = ∑' n : ℤ, ∫ α in (n : ℝ)..((n : ℝ) + 1), f α := by
  simpa only [zero_add] using (hf.hasSum_intervalIntegral 0).tsum_eq.symm
/-- P0082 page 356, auxiliary proof step. Every translate of an integrable function is interval integrable. -/
theorem translate_intervalIntegrable_supplied (f : ℝ → ℂ) (hf : Integrable f) (n : ℤ) :
    IntervalIntegrable (fun α : ℝ => f (α + n)) volume 0 1 :=
  (hf.comp_add_right (n : ℝ)).intervalIntegrable
/-- P0082 page 356, auxiliary proof step. The integrals of translated norms form a summable sequence. -/
theorem shift_norm_summable_supplied (f : ℝ → ℂ) (hf : Integrable f) :
    Summable (fun n : ℤ => ∫ α in (0 : ℝ)..1, ‖f (α + n)‖) :=
  hf.norm.hasSum_intervalIntegral_comp_add_int.summable
/-- P0082 page 356, auxiliary proof step. Integrate the translate series term by term under norm domination. -/
theorem interval_tsum_integral_supplied (f : ℝ → ℂ)
    (hint : ∀ n : ℤ, IntervalIntegrable (fun α : ℝ => f (α + n)) volume 0 1)
    (hsum : Summable (fun n : ℤ => ∫ α in (0 : ℝ)..1, ‖f (α + n)‖)) :
    (∫ α in (0 : ℝ)..1, ∑' n : ℤ, f (α + n)) =
      ∑' n : ℤ, ∫ α in (0 : ℝ)..1, f (α + n) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hsum ⊢
  symm
  apply integral_tsum_of_summable_integral_norm
  · intro n
    exact (hint n).1
  · exact hsum
/-- P0082 page 359, auxiliary proof step. Compare the constants and rates of two exponential decay bounds. -/
theorem decay_merge_supplied (κ κ' B B' X : ℝ) (N : ℕ)
    (hκ : 0 < κ) (hκ' : κ ≤ κ') (hB : 0 < B) (hB' : B ≤ B') (hX : 0 ≤ X) :
    B * N * Real.exp (-κ' * X) ≤ B' * N * Real.exp (-κ * X) := by
  have hBpos : 0 ≤ B' := hB.le.trans hB'
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hB' (Nat.cast_nonneg N)
  · apply Real.exp_le_exp.mpr
    nlinarith
  · positivity
  · positivity

end LeanLab.ExceptionalSet.Decomp462g

/-
P0087 Akeno 2026 page 6, the first step of the Type II estimate.
The exact finite Cauchy Schwarz inequality uses the cardinality of the m range.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Akeno2026.Cauchy86
open Finset

/-- LEAF. Page 6 first displayed inequality, with the exact finite cardinality. -/
theorem finite_cauchy {ι : Type*} (s : Finset ι) (A Z : ι → ℂ)
    (hA : ∀ i ∈ s, ‖A i‖ ≤ 1) :
    ‖∑ i ∈ s, A i * Z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖Z i‖ ^ 2 := by
  have hn : ‖∑ i ∈ s, A i * Z i‖ ≤ ∑ i ∈ s, ‖Z i‖ := by
    apply (norm_sum_le s _).trans
    apply sum_le_sum
    intro i hi
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hA i hi)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖Z i‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc

end LeanLab.Akeno2026.Cauchy86

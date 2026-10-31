/-
The finite family form of Schnirelmann's product inequality.
Source: Nathanson, arXiv:2407.12253v4, page 3, display after equation 1.
AI wrote this Lean code, OpenAI Codex, task26, 2026-10-22.
-/
import LeanLab.Schnirelmann.Inequality

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann

/-- The density deficit of a finite sumset is at most the product of the deficits. -/
theorem one_sub_density_sum_le (A : ℕ → Set ℕ) (h : ℕ)
    (hA : ∀ i < h, 0 ∈ A i) :
    1 - schnirelmannDensity (∑ i ∈ range h, A i) ≤
      ∏ i ∈ range h, (1 - schnirelmannDensity (A i)) := by
  have H : ∀ k : ℕ, (∀ i < k, 0 ∈ A i) →
      0 ∈ (∑ i ∈ range k, A i) ∧
      1 - schnirelmannDensity (∑ i ∈ range k, A i) ≤
        ∏ i ∈ range k, (1 - schnirelmannDensity (A i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      constructor
      · simp
      · simp only [range_zero, sum_empty, prod_empty]
        exact sub_le_self 1 schnirelmannDensity_nonneg
    | succ k ih =>
      intro hzero
      have hi := ih (fun i hi => hzero i (by omega))
      have hk : 0 ∈ A k := hzero k (by omega)
      rw [sum_range_succ, prod_range_succ]
      refine ⟨⟨0, hi.1, 0, hk, by simp⟩, ?_⟩
      calc
        1 - schnirelmannDensity ((∑ i ∈ range k, A i) + A k)
            ≤ (1 - schnirelmannDensity (∑ i ∈ range k, A i)) *
              (1 - schnirelmannDensity (A k)) :=
          one_sub_density_add_le _ _ hi.1 hk
        _ ≤ (∏ i ∈ range k, (1 - schnirelmannDensity (A i))) *
              (1 - schnirelmannDensity (A k)) :=
          mul_le_mul_of_nonneg_right hi.2 (sub_nonneg.mpr schnirelmannDensity_le_one)
  exact (H h hA).2

end LeanLab.Schnirelmann

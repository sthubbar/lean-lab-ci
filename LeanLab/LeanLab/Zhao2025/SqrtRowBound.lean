import Mathlib

/-!
The Cauchy Schwarz row bound used in display 3.7.
Source: Zhao 2025, display 3.7, page 9, using display 2.14 on page 5.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- Bounds on two nonnegative rows bound the row of square roots of their products. -/
theorem sqrt_row_bound {ι : Type*} (s : Finset ι) (g1 g2 : ι → ℝ) (B1 B2 : ℝ)
    (hg1 : ∀ j ∈ s, 0 ≤ g1 j) (hg2 : ∀ j ∈ s, 0 ≤ g2 j)
    (h1 : ∑ j ∈ s, g1 j ≤ B1) (h2 : ∑ j ∈ s, g2 j ≤ B2) :
    (∑ j ∈ s, Real.sqrt (g1 j * g2 j)) ≤ Real.sqrt (B1 * B2) := by
  have hp1 : 0 ≤ ∑ j ∈ s, g1 j := Finset.sum_nonneg hg1
  have hp2 : 0 ≤ ∑ j ∈ s, g2 j := Finset.sum_nonneg hg2
  have hsq1 : (∑ j ∈ s, Real.sqrt (g1 j) ^ 2) = ∑ j ∈ s, g1 j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.sq_sqrt (hg1 j hj)
  have hsq2 : (∑ j ∈ s, Real.sqrt (g2 j) ^ 2) = ∑ j ∈ s, g2 j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.sq_sqrt (hg2 j hj)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun j => Real.sqrt (g1 j)) (fun j => Real.sqrt (g2 j))
  rw [hsq1, hsq2] at hcs
  calc
    _ = ∑ j ∈ s, Real.sqrt (g1 j) * Real.sqrt (g2 j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Real.sqrt_mul (hg1 j hj) (g2 j)
    _ ≤ Real.sqrt (∑ j ∈ s, g1 j) * Real.sqrt (∑ j ∈ s, g2 j) := hcs
    _ = Real.sqrt ((∑ j ∈ s, g1 j) * ∑ j ∈ s, g2 j) := (Real.sqrt_mul hp1 _).symm
    _ ≤ Real.sqrt (B1 * B2) := Real.sqrt_le_sqrt (mul_le_mul h1 h2 hp2 (hp1.trans h1))

#print axioms sqrt_row_bound

end LeanLab.Zhao2025.Task56

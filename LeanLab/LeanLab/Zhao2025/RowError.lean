import LeanLab.Zhao2025.SqrtRowBound

/-!
An explicit relative budget for the additive error in display 2.14.
Source: Zhao 2025, displays 2.14 and 3.7, pages 5 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56

/-- A common additive row error becomes a relative square root error. -/
theorem row_error_bound {ι : Type*} (s : Finset ι) (g1 g2 : ι → ℝ)
    (B1 B2 delta eta : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (heta : 0 ≤ eta)
    (hd1 : delta ≤ eta * B1) (hd2 : delta ≤ eta * B2)
    (hg1 : ∀ j ∈ s, 0 ≤ g1 j) (hg2 : ∀ j ∈ s, 0 ≤ g2 j)
    (h1 : ∑ j ∈ s, g1 j ≤ B1 + delta) (h2 : ∑ j ∈ s, g2 j ≤ B2 + delta) :
    (∑ j ∈ s, Real.sqrt (g1 j * g2 j)) ≤ (1 + eta) * Real.sqrt (B1 * B2) := by
  have h1' : ∑ j ∈ s, g1 j ≤ (1 + eta) * B1 := by linarith
  have h2' : ∑ j ∈ s, g2 j ≤ (1 + eta) * B2 := by linarith
  have h := sqrt_row_bound s g1 g2 _ _ hg1 hg2 h1' h2'
  have he : 0 ≤ 1 + eta := by linarith
  calc
    _ ≤ Real.sqrt (((1 + eta) * B1) * ((1 + eta) * B2)) := h
    _ = Real.sqrt ((1 + eta) ^ 2 * (B1 * B2)) := by congr 1; ring
    _ = (1 + eta) * Real.sqrt (B1 * B2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq he]

#print axioms row_error_bound
end LeanLab.Zhao2025.Task56

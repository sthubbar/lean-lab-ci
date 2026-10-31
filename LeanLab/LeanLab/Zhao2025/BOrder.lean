import LeanLab.Zhao2025.BIntegralOrder

/-!
The nonnegativity and monotonicity of B are elementary.
Source: Zhao 2025, Lemma 2.3, displays 2.22 and 2.24, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- B is nonnegative and decreases with its positive lambda parameter. -/
theorem B_order (t l L l0 : ℝ) (ht : 0 ≤ t) (hl : 0 < l) (h0 : 0 < l0) (hL : l ≤ L) :
    0 ≤ B t l l0 ∧ B t L l0 ≤ B t l l0 := by
  have h := BLaplace_order t l L l0 ht h0 hL
  constructor
  · rw [B_eq_laplace t l l0 hl h0]
    exact h.1
  · rw [B_eq_laplace t L l0 (hl.trans_le hL) h0, B_eq_laplace t l l0 hl h0]
    exact h.2

#print axioms B_order

end LeanLab.Zhao2025.Task56

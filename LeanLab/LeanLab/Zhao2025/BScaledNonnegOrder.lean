import LeanLab.Zhao2025.BScaledOrder
import LeanLab.Zhao2025.BZeroScaledOrder

/-!
Both lambda0 branches of the scaled monotonicity argument combined.
Source: Zhao 2025, Lemma 2.3, pages 6 and 7.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- Scaled B is monotone for every nonnegative lambda0. -/
theorem B_scaled_nonneg_order (t l L l0 : ℝ) (ht : 0 ≤ t) (hl : 0 < l)
    (h0 : 0 ≤ l0) (hL : l ≤ L) :
    Real.exp (l * t) * B t l l0 ≤ Real.exp (L * t) * B t L l0 := by
  by_cases hz : l0 = 0
  · subst l0
    exact B_zero_scaled_order t l L ht hl hL
  · exact B_scaled_order t l L l0 ht hl (lt_of_le_of_ne h0 (Ne.symm hz)) hL

#print axioms B_scaled_nonneg_order

end LeanLab.Zhao2025.Task56

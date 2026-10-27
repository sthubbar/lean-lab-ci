import LeanLab.Zhao2025.BOrder
import LeanLab.Zhao2025.BZeroOrder

/-!
The two lambda0 branches in the proof of Lemma 2.3 combined.
Source: Zhao 2025, displays 2.19 to 2.24, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- B is nonnegative and antitone for every nonnegative lambda0 and positive lambda. -/
theorem B_nonneg_order (t l L l0 : ℝ) (ht : 0 ≤ t) (hl : 0 < l) (h0 : 0 ≤ l0) (hL : l ≤ L) :
    0 ≤ B t l l0 ∧ B t L l0 ≤ B t l l0 := by
  by_cases hz : l0 = 0
  · subst l0
    exact B_zero_order t l L ht hl hL
  · exact B_order t l L l0 ht hl (lt_of_le_of_ne h0 (Ne.symm hz)) hL

#print axioms B_nonneg_order

end LeanLab.Zhao2025.Task56

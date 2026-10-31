import LeanLab.Zhao2025.BPositive

/-!
A row error budget uniform on a bounded positive lambda interval.
Source: Zhao 2025, display 2.14 on page 5 and its use in 3.7 on page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6825

/-- The additive row error can be chosen before any lambda in the bounded family. -/
theorem uniform_row_budget (t1 t2 H l0 eta : ℝ)
    (ht1 : 0 < t1) (ht2 : 0 < t2) (hH : 0 < H) (h0 : 0 ≤ l0) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ l : ℝ, 0 < l → l ≤ H →
      delta ≤ eta * B t1 l l0 ∧ delta ≤ eta * B t2 l l0 := by
  refine ⟨eta * min (B t1 H l0) (B t2 H l0), ?_, ?_⟩
  · exact mul_pos heta (lt_min (B_positive t1 H l0 ht1 hH h0)
      (B_positive t2 H l0 ht2 hH h0))
  · intro l hl hlH
    constructor
    · exact mul_le_mul_of_nonneg_left
        ((min_le_left _ _).trans (B_nonneg_order t1 l H l0 ht1.le hl h0 hlH).2) heta.le
    · exact mul_le_mul_of_nonneg_left
        ((min_le_right _ _).trans (B_nonneg_order t2 l H l0 ht2.le hl h0 hlH).2) heta.le

#print axioms uniform_row_budget
end LeanLab.Zhao2025.Task56

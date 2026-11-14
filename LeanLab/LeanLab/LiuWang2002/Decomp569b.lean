import LeanLab.LiuWang2002.CheckData569b

/-!
Strictly smaller supplies for the sealed Decomp460b leaf.
Source Schoenfeld page 356, display 5.1 star, derived integer bounds.
The endpoint state and remaining tail are OPEN.
The assembly is CONDITIONAL ON those two obligations.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task569
open Task368

/-- LEAF. Exact initial prime product invariant at 8000000.
This single endpoint is smaller than the assigned range.
Source page 356, display 5.1 star, derived sufficient state. -/
theorem initial569b :
    primorial 8000000 * 25 ^ 8000000 * checkpointScale ≤ 1 * 68 ^ 8000000 := by
  sorry

/-- LEAF. Integer certificate strictly above 8016384 through 12000000.
This tail is a proper subrange of Task460.primorial_c4_lower.
Source page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c4_lower_tail (n : ℕ) (hn : 8016384 < n) (hn' : n ≤ 12000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- The checked part and open tail have concrete integer witnesses.
The join belongs only to the checked part.
Source page 356, display 5.1 star, derived domains. -/
theorem domains569b :
    (8000000 < (8000001 : ℕ) ∧ 8000001 ≤ 8016384) ∧
    (8016384 < (8016385 : ℕ) ∧ 8016385 ≤ 12000000) ∧
    (8000000 < (8016384 : ℕ) ∧ 8016384 ≤ 8016384) ∧ ¬ 8016384 < (8016384 : ℕ) := by
  norm_num

/-- Exact supply for Task460.primorial_c4_lower.
CONDITIONAL ON initial569b and primorial_c4_lower_tail.
Source page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c4_lower (n : ℕ) (hn : 8000000 < n) (hn' : n ≤ 12000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 8016384
  · exact range569b initial569b n hn hm
  · exact primorial_c4_lower_tail n (by omega) hn'

end LeanLab.LiuWang2002.Task569
#print axioms LeanLab.LiuWang2002.Task569.initial569b
#print axioms LeanLab.LiuWang2002.Task569.primorial_c4_lower_tail
#print axioms LeanLab.LiuWang2002.Task569.domains569b
#print axioms LeanLab.LiuWang2002.Task569.primorial_c4_lower

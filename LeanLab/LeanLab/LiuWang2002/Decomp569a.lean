import LeanLab.LiuWang2002.CheckData569a

/-!
Strictly smaller supplies for the sealed Decomp460b leaf.
Source Schoenfeld page 356, display 5.1 star, derived integer bounds.
The endpoint state and remaining tail are OPEN.
The assembly is CONDITIONAL ON those two obligations.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task569
open Task368

/-- LEAF. Exact initial prime product invariant at 6000000.
This single endpoint is smaller than the assigned range.
Source page 356, display 5.1 star, derived sufficient state. -/
theorem initial569a :
    primorial 6000000 * 25 ^ 6000000 * checkpointScale ≤ 1 * 68 ^ 6000000 := by
  sorry

/-- LEAF. Integer certificate strictly above 6016384 through 8000000.
This tail is a proper subrange of Task460.primorial_c3_upper.
Source page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c3_upper_tail (n : ℕ) (hn : 6016384 < n) (hn' : n ≤ 8000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- The checked part and open tail have concrete integer witnesses.
The join belongs only to the checked part.
Source page 356, display 5.1 star, derived domains. -/
theorem domains569a :
    (6000000 < (6000001 : ℕ) ∧ 6000001 ≤ 6016384) ∧
    (6016384 < (6016385 : ℕ) ∧ 6016385 ≤ 8000000) ∧
    (6000000 < (6016384 : ℕ) ∧ 6016384 ≤ 6016384) ∧ ¬ 6016384 < (6016384 : ℕ) := by
  norm_num

/-- Exact supply for Task460.primorial_c3_upper.
CONDITIONAL ON initial569a and primorial_c3_upper_tail.
Source page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c3_upper (n : ℕ) (hn : 6000000 < n) (hn' : n ≤ 8000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 6016384
  · exact range569a initial569a n hn hm
  · exact primorial_c3_upper_tail n (by omega) hn'

end LeanLab.LiuWang2002.Task569
#print axioms LeanLab.LiuWang2002.Task569.initial569a
#print axioms LeanLab.LiuWang2002.Task569.primorial_c3_upper_tail
#print axioms LeanLab.LiuWang2002.Task569.domains569a
#print axioms LeanLab.LiuWang2002.Task569.primorial_c3_upper

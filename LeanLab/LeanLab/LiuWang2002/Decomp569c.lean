import LeanLab.LiuWang2002.CheckData569c

/-!
Strictly smaller supplies for the sealed Decomp460b leaf.
Source Schoenfeld page 356, display 5.1 star, derived integer bounds.
The endpoint state and remaining tail are OPEN.
The assembly is CONDITIONAL ON those two obligations.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task569
open Task368

/-- LEAF. Exact initial prime product invariant at 12000000.
This single endpoint is smaller than the assigned range.
Source page 356, display 5.1 star, derived sufficient state. -/
theorem initial569c :
    primorial 12000000 * 25 ^ 12000000 * checkpointScale ≤ 1 * 68 ^ 12000000 := by
  sorry

/-- LEAF. Integer certificate strictly above 12016384 through 16000000.
This tail is a proper subrange of Task460.primorial_c4_upper.
Source page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c4_upper_tail (n : ℕ) (hn : 12016384 < n) (hn' : n ≤ 16000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  sorry

/-- The checked part and open tail have concrete integer witnesses.
The join belongs only to the checked part.
Source page 356, display 5.1 star, derived domains. -/
theorem domains569c :
    (12000000 < (12000001 : ℕ) ∧ 12000001 ≤ 12016384) ∧
    (12016384 < (12016385 : ℕ) ∧ 12016385 ≤ 16000000) ∧
    (12000000 < (12016384 : ℕ) ∧ 12016384 ≤ 12016384) ∧ ¬ 12016384 < (12016384 : ℕ) := by
  norm_num

/-- Exact supply for Task460.primorial_c4_upper.
CONDITIONAL ON initial569c and primorial_c4_upper_tail.
Source page 356, display 5.1 star, derived integer certificate. -/
theorem primorial_c4_upper (n : ℕ) (hn : 12000000 < n) (hn' : n ≤ 16000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  by_cases hm : n ≤ 12016384
  · exact range569c initial569c n hn hm
  · exact primorial_c4_upper_tail n (by omega) hn'

end LeanLab.LiuWang2002.Task569
#print axioms LeanLab.LiuWang2002.Task569.initial569c
#print axioms LeanLab.LiuWang2002.Task569.primorial_c4_upper_tail
#print axioms LeanLab.LiuWang2002.Task569.domains569c
#print axioms LeanLab.LiuWang2002.Task569.primorial_c4_upper

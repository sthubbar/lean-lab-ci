import LeanLab.Zhao2025.Theorem12

/-!
The reviewed wrapper does not constrain S in its last case.
This is an obstruction in the wrapper interface, not a claim about Zhao's paper.
Source: display 1.10, page 3, https://arxiv.org/abs/2511.05631v2.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6900 LeanLab.Zhao2025.U6837

/-- The wrapper inputs permit a square sum of eight. -/
theorem wrapper_obstruction :
    Lemma24_dichotomy 1 0.7 (fun _ => 0) (fun _ => 0) (fun _ => 2) ∧
    ∑ i ∈ Finset.range 2, (2 : ℝ) ^ 2 = 8 := by
  constructor
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    refine ⟨by norm_num, fun _ => le_rfl, fun _ => le_rfl, ?_, ?_, Or.inl ?_⟩
    · norm_num
    · norm_num
    · intro i
      simp only [hd]
      split_ifs <;> norm_num
  · norm_num [Finset.sum_range_succ]

#print axioms wrapper_obstruction

end LeanLab.Zhao2025.Task56

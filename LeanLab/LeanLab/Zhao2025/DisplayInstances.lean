import LeanLab.Zhao2025.Display110Wrapper

/-!
Nonempty arithmetic instances of the conditional display inputs.
These are finite abstract real lambda data.
They do not assert that a Dirichlet L zero exists.
Source: Zhao 2025, display 1.10 on page 3 and the last case on page 16.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6837

/-- One positive tail value satisfies every bound in the last case. -/
theorem nonempty_case_inputs :
    CaseInputs 10 1 1 (fun _ => 0) (fun _ => Real.exp (-(10 / 3))) (fun _ => 0) := by
  have he : Real.exp (-(10 / 3 : ℝ)) ≤ 0.0465761503 :=
    (Real.exp_le_exp.mpr (by norm_num)).trans x4615.2
  refine ⟨by norm_num, fun _ => le_rfl, fun _ => (Real.exp_pos _).le, ?_, ?_, Or.inl ?_⟩
  · norm_num
  · norm_num [Finset.sum_range_succ]
    linarith
  · intro i
    constructor
    · simp only [hd]
      split_ifs <;> norm_num
    · simp only [hd]
      split_ifs <;> linarith

#print axioms nonempty_case_inputs

/-- The same nonempty input is realized by a singleton of abstract real lambda data. -/
theorem nonempty_zero_inputs :
    CaseInputs 10 1 1
      (fun _ => residualSum ({()} : Finset Unit) (fun _ => 1) 1)
      (fun _ => cappedSum ({()} : Finset Unit) (fun _ => 1) 1)
      (fun _ => zeroSum (∅ : Finset Unit) (fun _ => 1)) := by
  simpa [residualSum, zeroSum, cappedSum] using nonempty_case_inputs

#print axioms nonempty_zero_inputs

end LeanLab.Zhao2025.Task56

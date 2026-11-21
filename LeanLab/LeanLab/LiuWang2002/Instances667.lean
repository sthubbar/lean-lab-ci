import LeanLab.LiuWang2002.Decomp1543c

/-!
A nonempty resonant domain instance for Liu and Wang Lemma 6.4 on page 169.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task667
open LeanLab.LiuWang2002.U1543

/-- The Lemma 6.4 domain includes an integral phase at the final summand.
The existing minK convention returns its first argument at that phase. -/
theorem resonant_instance :
    Dioph (1 / 15) 1 15 ∧ 15 ≤ (15 : ℕ) ∧ 1 ≤ (15 : ℝ) ∧ 0 < (15 : ℝ) ∧
      minK (15 / 15) ((1 / 15) * 15) = 1 := by
  refine ⟨wcLemma3_hyps_hold.1, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [minK, nint]

end LeanLab.LiuWang2002.Task667
#print axioms LeanLab.LiuWang2002.Task667.resonant_instance

import LeanLab.Zhao2025.GDenominator
import LeanLab.Zhao2025.Zhao2025U6902R

/-!
The normalized Laplace ratio decreases with its cutoff.
Source: Zhao 2025, display 3.23, page 10.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6841 LeanLab.Zhao2025.U6900

/-- The normalized psi ratio is antitone for positive x and nonnegative lambda0. -/
theorem psiR_antitone (x l0 : ℝ) (hx : 0 < x) (h0 : 0 ≤ l0) : Antitone (fun L => psiR x L l0) := by
  intro L U hLU
  have hd := Gz_negative_lower (-l0 / x) (div_nonpos_of_nonpos_of_nonneg (by linarith) hx.le)
  have hp : 0 ≤ Gz (-l0 / x) := by linarith
  have hm := (Gz_order ((L - l0) / x) ((U - l0) / x)
    (div_le_div_of_nonneg_right (by linarith) hx.le)).2
  exact div_le_div_of_nonneg_right hm hp

#print axioms psiR_antitone
end LeanLab.Zhao2025.Task56

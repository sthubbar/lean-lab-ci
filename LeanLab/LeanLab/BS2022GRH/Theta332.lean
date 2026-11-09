/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Reuse the existing Buthe input to supply journal Lemma 2.
Buthe Theorem 2 p. 2 display 1.7. https://arxiv.org/abs/1511.02032
Journal pp. 1215 and 1220. https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.ThetaInputs224

namespace LeanLab.BS2022GRH.Theta332
open Real

/-- The existing Buthe sign estimate implies the entire finite theta cap of Lemma 2.
Journal p. 1215 and Buthe p. 2 display 1.7. CONDITIONAL ON the explicit input.
Below one use Mathlib theta_eq_zero_of_le_one. No computation is asserted as proved. -/
theorem theta_of_buthe
    (hB : ∀ x : ℝ, 1 ≤ x → x ≤ 1e19 → (0.05 : ℝ) * √x < x - Chebyshev.theta x) :
    PaperInputs148.Lemma2J := by
  intro x hx hxcap
  by_cases h1 : 1 ≤ x
  · have h := hB x h1 (by linarith)
    nlinarith [sqrt_nonneg x]
  · rw [Chebyshev.theta_eq_zero_of_le_one (lt_of_not_ge h1).le]
    exact hx.le

end LeanLab.BS2022GRH.Theta332
#print axioms LeanLab.BS2022GRH.Theta332.theta_of_buthe

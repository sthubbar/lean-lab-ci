import LeanLab.Zhao2025.CountFrom34
import LeanLab.Zhao2025.Equation313

/-!
An epsilon retaining variant of display 3.13 for the actual finite zero count.
Source: Zhao 2025, displays 3.4, 3.12 and 3.13, pages 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON display 3.4, with its epsilon factor retained. -/
theorem eq313_from34 {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (h34 : ∀ L, 1.311 ≤ L →
      weightedCappedSum (8 / 3) s lam L ≤
        (1 + epsilon) * C (1 / 12) (1 / 4) (1 / 6) L (1 / 2)) :
    ∀ L, 1.311 ≤ L → ((s.filter fun j => lam j ≤ L).card : ℝ) ≤
      (1 + epsilon) * 19.62 * Real.exp (8 / 3 * L) := by
  apply eq313_actual_conditional (fun L => ((s.filter fun j => lam j ≤ L).card : ℝ)) epsilon he
  intro L hL
  exact count_from34 s lam (8 / 3) (1 / 12) (1 / 4) (1 / 6) L (1 / 2) epsilon (h34 L hL)

#print axioms eq313_from34

end LeanLab.Zhao2025.Task56

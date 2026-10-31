import LeanLab.Zhao2025.T5From325
import LeanLab.Zhao2025.Cor32From34

/-!
The layout C t5 input depends on 3.25 and 3.4, with the remaining elementary steps proved.
Source: Zhao 2025, displays 3.4, 3.16 and 3.25 to 3.27, pages 8, 10 and 11.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6825 LeanLab.Zhao2025.U6841 LeanLab.Zhao2025.U6900

/-- CONDITIONAL ON the two stated analytic display inputs. -/
theorem t5_from325_and34 {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (e : ℝ)
    (he0 : 0 ≤ e) (he : e ≤ 1 / 10 ^ 8)
    (h325 : ∀ L x : ℝ, 1.363 ≤ L → L ≤ 5.2 → 4 * 0.857 / 5 ≤ x →
      0 < Delta x L 0.857 → e < Delta x L 0.857 ^ 2 →
      (Delta x L 0.857 ^ 2 - e) * ((s.filter fun j => lam j ≤ L).card : ℝ) +
        2 * Delta x L 0.857 * densityExcess s lam x L 0.857 ≤ 1)
    (h34 : ∀ L, 5.2 ≤ L → weightedCappedSum (833 / 750) s lam L ≤
      (1 + e) * C 0.029 0.083 0.052 L 0) : cappedSum s lam 1.363 ≤ 0.09063 := by
  have htail := (cor32_from34 s lam e he0 (by linarith) h34 5.2 le_rfl).2
  exact t5_from325 s lam e he0 he h325 htail

#print axioms t5_from325_and34
end LeanLab.Zhao2025.Task56

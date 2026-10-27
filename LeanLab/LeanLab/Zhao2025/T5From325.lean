import LeanLab.Zhao2025.DensityExcess
import LeanLab.Zhao2025.CountFrom325
import LeanLab.Zhao2025.Zhao2025U6900Abel

/-!
The existing certified grid uses display 3.25 directly after the elementary count step.
The source density input is used only in its strict interior domain.
Source: Zhao 2025, displays 3.25 to 3.27, page 11.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6841 LeanLab.Zhao2025.U6900

/-- CONDITIONAL ON 3.25 and the terminal bound 3.20, with all grid counts certified. -/
theorem t5_from325 {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (e : ℝ)
    (he0 : 0 ≤ e) (he : e ≤ 1 / 10 ^ 8)
    (h325 : ∀ L x : ℝ, 1.363 ≤ L → L ≤ 5.2 → 4 * 0.857 / 5 ≤ x →
      0 < Delta x L 0.857 → e < Delta x L 0.857 ^ 2 →
      (Delta x L 0.857 ^ 2 - e) * ((s.filter fun j => lam j ≤ L).card : ℝ) +
        2 * Delta x L 0.857 * densityExcess s lam x L 0.857 ≤ 1)
    (h320 : Tsum s lam 5.2 ≤ 0.001) : Tsum s lam 1.363 ≤ 0.09063 := by
  apply t5_of_326 s lam e he _ h320
  intro L x hL hU hx hd hgap
  exact count_from325 _ _ _ e
    (density_excess_nonneg s lam x L 0.857 (by linarith) (by norm_num))
    hd.le hgap (h325 L x hL hU hx hd hgap)

#print axioms t5_from325
end LeanLab.Zhao2025.Task56

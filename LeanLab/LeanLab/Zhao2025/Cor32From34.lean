import LeanLab.Zhao2025.Eq315From34
import LeanLab.Zhao2025.Cor32Actual

/-!
Corollary 3.2 conditional only on the finite weighted sum bound in Lemma 3.1.
Source: Zhao 2025, displays 3.4 and 3.15 to 3.19, pages 8 and 10.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON display 3.4 alone, with the printed M bounded exponent. -/
theorem cor32_from34 {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 0.001)
    (h34 : ∀ L, 5.2 ≤ L → weightedCappedSum (833 / 750) s lam L ≤
      (1 + epsilon) * C 0.029 0.083 0.052 L 0) :
    ∀ L, 5.2 ≤ L → cappedSum s lam L ≤ 100 * Real.exp (-2.22 * L) ∧
      cappedSum s lam L ≤ 0.001 := by
  apply cor32_actual_conditional (fun L => cappedSum s lam L) epsilon he0 he1
  intro L hL
  have hb := eq315_from34 s lam (833 / 750) 0.029 0.083 0.052 L 0 epsilon
    (by constructor <;> norm_num) (h34 L hL)
  have he : (10 / 3 - 833 / 750 : ℝ) = 3334 / 1500 := by norm_num
  rw [he] at hb
  calc
    _ ≤ (1 + epsilon) * (Real.exp (-(3334 / 1500 * L)) * C 0.029 0.083 0.052 L 0) := hb
    _ = _ := by ring

#print axioms cor32_from34

end LeanLab.Zhao2025.Task56

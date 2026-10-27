import LeanLab.Zhao2025.CountFrom34
import LeanLab.Zhao2025.CMonotone
import LeanLab.Zhao2025.C313Tighter

/-!
The printed coefficient in display 3.13, with epsilon explicitly absorbed.
The only analytic input is Lemma 3.1, display 3.4, at the printed parameters.
Source: Zhao 2025, displays 3.4 and 3.13, pages 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON display 3.4 alone, with the exact printed constant 19.62. -/
theorem eq313_exact_from34 {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 0.0001)
    (h34 : ∀ L, 1.311 ≤ L → weightedCappedSum (8 / 3) s lam L ≤
      (1 + epsilon) * C (1 / 12) (1 / 4) (1 / 6) L (1 / 2)) :
    ∀ L, 1.311 ≤ L → ((s.filter fun j => lam j ≤ L).card : ℝ) ≤
      19.62 * Real.exp (8 / 3 * L) := by
  intro L hL
  have hN := count_from34 s lam (8 / 3) (1 / 12) (1 / 4) (1 / 6) L (1 / 2) epsilon (h34 L hL)
  have hC : C (1 / 12) (1 / 4) (1 / 6) L (1 / 2) ≤ 19.612 :=
    (C_antitone _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hL).trans C313_tighter
  have hA : (1 + epsilon) * C (1 / 12) (1 / 4) (1 / 6) L (1 / 2) ≤ 19.62 := by
    calc
      _ ≤ (1 + epsilon) * 19.612 := mul_le_mul_of_nonneg_left hC (by linarith)
      _ ≤ 19.62 := by nlinarith
  exact hN.trans (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le)

#print axioms eq313_exact_from34

end LeanLab.Zhao2025.Task56

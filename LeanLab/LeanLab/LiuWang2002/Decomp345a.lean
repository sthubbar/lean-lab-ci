import LeanLab.LiuWang2002.Decomp1543c

/-!
Task345. Endpoint bookkeeping for Lemma 6.2 on page 169.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task345

open Real Finset ArithmeticFunction U1543

/-- The inclusive Mangoldt sum in Lemma 6.2, page 169, equals Mathlib psi.
The zero term vanishes. This is endpoint bookkeeping for the displayed proof. -/
theorem psi_eq_sum_range (X : ℝ) :
    Chebyshev.psi X = ∑ n ∈ Finset.range (Nat.floor X + 1), (vonMangoldt n : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]

/-- Lemma 6.2 on page 169 from the explicitly supplied psi component.
The triangle, parameter threshold and root absorption steps already exist
in Decomp1543c and Decomp109b. CONDITIONAL ON hPsi. -/
theorem lemma62_S1_of_psi (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ)
    (hPsi : Chebyshev.psi (Uf N) ≤
      1.001102 * (Uf N + (Uf N) ^ (1 / 2 : ℝ)) + 3 * (Uf N) ^ (1 / 3 : ℝ)) :
    ‖Ssum (lam1 (Uf N)) c N α‖ ≤ 1.02 * Uf N := by
  have hNp := (task141_logs N hL).1
  have hNlarge : exp 30.95 ≤ (N : ℝ) :=
    (le_log_iff_exp_le hNp).mp (by linarith)
  have hU : exp 9.634 ≤ Uf N := by
    simpa only [Vaughan109.U, Uf, neg_div] using Decomp109b.U_lower (N : ℝ) hNlarge
  calc
    _ ≤ ∑ n ∈ Icc 1 ⌊Uf N⌋₊, (vonMangoldt n : ℝ) := task147_S1_triangle c N (Uf N) α
    _ = Chebyshev.psi (Uf N) := by rfl
    _ ≤ _ := hPsi
    _ ≤ _ := Decomp109b.root_absorb (Uf N) hU

end LeanLab.LiuWang2002.Task345

#print axioms LeanLab.LiuWang2002.Task345.psi_eq_sum_range

#print axioms LeanLab.LiuWang2002.Task345.lemma62_S1_of_psi

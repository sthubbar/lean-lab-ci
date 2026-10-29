/-
AI wrote the Lean code.
Decomposition of Theorem 6, p. 1231.
-/
import Mathlib
import LeanLab.BS2022GRH.ChenThresholdGRH
import LeanLab.BS2022GRH.Params
import LeanLab.BS2022GRH.U7154UN
import LeanLab.DERZ1997.Statements

open Real Finset

/-- LEAF p.1231: Upper bound factor for S(A_q, P, z) with generic X₂ -/
lemma leaf_b6_eq (α A ε C₁ X₂ N : ℝ) :
  LeanLab.BS2022GRH.ChenThresholdGRH.B6J α A ε C₁ X₂ N = LeanLab.BS2022GRH.ChenThresholdGRH.l1J α ε C₁ X₂ + LeanLab.BS2022GRH.ChenThresholdGRH.l2J X₂ / log N ^ (A - 3) + LeanLab.BS2022GRH.ChenThresholdGRH.l3J α ε C₁ X₂ / log N ^ (A - 1) := by
  rfl

/-- LEAF p.1231: Core combination step -/
lemma leaf_comb_thm6 (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ)
  (hGRH : LeanLab.DERZ1997.GRH) (hSieve : LeanLab.BS2022GRH.ChenThresholdGRH.LinearSieveT4 ε C₁ C₂) (heps : LeanLab.BS2022GRH.ChenThresholdGRH.epsJ u ≤ ε)
  (halpha1 : 0 < α) (halpha2 : α < 1 / 24) (hA : 0 < A) (hCond : LeanLab.BS2022GRH.ChenThresholdGRH.Cond19 α A u X₂)
  (hX2X : exp (exp 10) ≤ X₂) (hX2N : X₂ ≤ (n : ℝ))
  (heq : LeanLab.BS2022GRH.ChenThresholdGRH.B6J α A ε C₁ X₂ n = LeanLab.BS2022GRH.ChenThresholdGRH.l1J α ε C₁ X₂ + LeanLab.BS2022GRH.ChenThresholdGRH.l2J X₂ / log (n : ℝ) ^ (A - 3) + LeanLab.BS2022GRH.ChenThresholdGRH.l3J α ε C₁ X₂ / log (n : ℝ) ^ (A - 1)) :
  ∑ q ∈ (LeanLab.BS2022GRH.U7153.Qset n).filter (fun q => ¬ q ∣ n), (LeanLab.BS2022GRH.U7153.SAq n q : ℝ)
      ≤ 8 * (LeanLab.BS2022GRH.UNfull n * n / log n ^ 2) * LeanLab.BS2022GRH.ChenThresholdGRH.B6J α A ε C₁ X₂ n := by
  sorry

/-- **Theorem 6**, pp. 1231-1232: Σ_{z ≤ q < y, q ∤ N} S(A_q, ℙ, z) ≤ 8 U_N N/log² N · B6. -/
theorem thm6J_assembly : LeanLab.BS2022GRH.ChenThresholdGRH.Thm6J := by
  intro α A u ε C₁ C₂ X₂ n hGRH hSieve heps halpha1 halpha2 hA hCond hX2X hX2N
  apply leaf_comb_thm6 α A u ε C₁ C₂ X₂ n hGRH hSieve heps halpha1 halpha2 hA hCond hX2X hX2N
  exact leaf_b6_eq α A ε C₁ X₂ n

/-
AI wrote the Lean code.
Decomposition of Theorem 5, p. 1228.
-/
import Mathlib
import LeanLab.BS2022GRH.ChenThresholdGRH
import LeanLab.BS2022GRH.Params
import LeanLab.BS2022GRH.U7154UN
import LeanLab.DERZ1997.Statements

open Real

/-- LEAF p.1228: Upper bound factor for S(A, P, z) with generic X₂ -/
lemma leaf2_bracket (α A ε C₂ X₂ N : ℝ) :
  LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ N = (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
      (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α)
        - ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α)))
    - 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ * LeanLab.BS2022GRH.ChenThresholdGRH.invTw * LeanLab.BS2022GRH.ChenThresholdGRH.cGJ X₂ / log N ^ (A - 2) := by
  rfl

/-- LEAF p.1228: Core combination step -/
lemma leaf_comb (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ)
  (hGRH : LeanLab.DERZ1997.GRH) (hSieve : LeanLab.BS2022GRH.ChenThresholdGRH.LinearSieveT4 ε C₁ C₂) (heps : LeanLab.BS2022GRH.ChenThresholdGRH.epsJ u ≤ ε)
  (halpha1 : 0 < α) (halpha2 : α < 1 / 8) (hA : 0 < A) (hCond : LeanLab.BS2022GRH.ChenThresholdGRH.Cond19 α A u X₂)
  (hX2X : 4e18 ≤ X₂) (hX2N : X₂ ≤ (n : ℝ))
  (heq : LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ n = (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
      (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α)
        - ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α)))
    - 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ * LeanLab.BS2022GRH.ChenThresholdGRH.invTw * LeanLab.BS2022GRH.ChenThresholdGRH.cGJ X₂ / log (n:ℝ) ^ (A - 2)) :
  8 * (LeanLab.BS2022GRH.UNfull n * n / log n ^ 2) * LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ n < (LeanLab.BS2022GRH.U7153.SA n : ℝ) := by
  sorry

/-- **Theorem 5**, p. 1228: S(A, ℙ, z) > 8 U_N N/log² N · B5. -/
theorem thm5J_assembly : LeanLab.BS2022GRH.ChenThresholdGRH.Thm5J := by
  intro α A u ε C₁ C₂ X₂ n hGRH hSieve heps halpha1 halpha2 hA hCond hX2X hX2N
  apply leaf_comb α A u ε C₁ C₂ X₂ n hGRH hSieve heps halpha1 halpha2 hA hCond hX2X hX2N
  exact leaf2_bracket α A ε C₂ X₂ n

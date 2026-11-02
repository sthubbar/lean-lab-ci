/-
Unit U-1601, statement audit of BS2022GRH DecompJ215.leaf_comb.
AI wrote this Lean code. Goldbach is open.
The sealed leaf is logically the same as the negation of GRH, so proving it is not a route.
The repaired hypothesis list is exactly Thm5J.
-/
import LeanLab.BS2022GRH.DecompJ215

namespace LeanLab.BS2022GRH.Audit1601

open Real LeanLab.BS2022GRH.ChenThresholdGRH

/-- The word for word statement of DecompJ215.leaf_comb. -/
def LeafCombStatement : Prop :=
  ∀ (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ), LeanLab.DERZ1997.GRH → LinearSieveT4 ε C₁ C₂ →
    epsJ u ≤ ε → 0 < α → α < 1 / 8 → 0 < A → Cond19 α A u X₂ →
    4e18 ≤ X₂ → X₂ ≤ (n : ℝ) →
    B5J α A ε C₂ X₂ n = (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
        (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α)
          - ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α)))
      - 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ * invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2) →
    8 * (LeanLab.BS2022GRH.UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n <
      (LeanLab.BS2022GRH.U7153.SA n : ℝ)

/-- The sealed leaf holds exactly when GRH fails. It takes GRH as a hypothesis, so one
direction is immediate, and the other is leaf_comb_excludes_GRH. -/
theorem leafComb_iff_not_GRH : LeafCombStatement ↔ ¬ LeanLab.DERZ1997.GRH := by
  constructor
  · intro h
    apply leaf_comb_excludes_GRH
    intro α A u ε C₁ C₂ X₂ n hG hS hE h1 h2 h3 h4 h5 h6
    exact h α A u ε C₁ C₂ X₂ n hG hS hE h1 h2 h3 h4 h5 h6 (leaf2_bracket α A ε C₂ X₂ n)
  · intro hG α A u ε C₁ C₂ X₂ n hGRH
    exact absurd hGRH hG

/-- The repaired leaf: the five guards of the sealed Thm5J are added. -/
def LeafCombRepaired : Prop :=
  ∀ (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ), LeanLab.DERZ1997.GRH → LinearSieveT4 ε C₁ C₂ →
    0 ≤ C₁ → 0 ≤ C₂ → epsJ u ≤ ε → 0 < ε → ε < 1 / 63 →
    0 < α → α < 1 / 8 → 0 < A → Cond19 α A u X₂ →
    4e18 ≤ X₂ → X₂ ≤ (n : ℝ) → Even n →
    B5J α A ε C₂ X₂ n = (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
        (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α)
          - ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α)))
      - 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ * invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2) →
    8 * (LeanLab.BS2022GRH.UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n <
      (LeanLab.BS2022GRH.U7153.SA n : ℝ)

/-- The repaired leaf is exactly the sealed Thm5J, with the rfl bracket equation removed. -/
theorem leafCombRepaired_iff_Thm5J : LeafCombRepaired ↔ Thm5J := by
  constructor
  · intro h α A u ε C₁ C₂ X₂ n hG hS hC1 hC2 hE he0 he1 h1 h2 h3 h4 h5 h6 hev
    exact h α A u ε C₁ C₂ X₂ n hG hS hC1 hC2 hE he0 he1 h1 h2 h3 h4 h5 h6 hev
      (leaf2_bracket α A ε C₂ X₂ n)
  · intro h α A u ε C₁ C₂ X₂ n hG hS hC1 hC2 hE he0 he1 h1 h2 h3 h4 h5 h6 hev _
    exact h α A u ε C₁ C₂ X₂ n hG hS hC1 hC2 hE he0 he1 h1 h2 h3 h4 h5 h6 hev

end LeanLab.BS2022GRH.Audit1601

#print axioms LeanLab.BS2022GRH.Audit1601.leafComb_iff_not_GRH
#print axioms LeanLab.BS2022GRH.Audit1601.leafCombRepaired_iff_Thm5J

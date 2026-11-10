/-
AI wrote the Lean code.
Decomposition of Theorem 5, p. 1228.
-/
import Mathlib
import LeanLab.BS2022GRH.ChenThresholdGRH
import LeanLab.BS2022GRH.Params
import LeanLab.BS2022GRH.U7154UN
import LeanLab.BS2022GRH.Decomp138b
import LeanLab.DERZ1997.Statements
import LeanLab.BS2022GRH.Decomp333a

open Real

/-- LEAF p.1228: Upper bound factor for S(A, P, z) with generic X₂ -/
lemma leaf2_bracket (α A ε C₂ X₂ N : ℝ) :
  LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ N = (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
      (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α)
        - ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α)))
    - 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ * LeanLab.BS2022GRH.ChenThresholdGRH.invTw * LeanLab.BS2022GRH.ChenThresholdGRH.cGJ X₂ / log N ^ (A - 2) := by
  rfl

/-- The unrepaired leaf_comb, kept here as the quantified hypothesis below, was FALSE. Its hypothesis list was verbatim the archived pre-fix Theorem 5 of
Decomp138b, `Thm5JOld`, which the U-1580 audit refutes given GRH: at ε = 1 the sieve
hypothesis of `LinearSieveT4` is vacuous and `sieve_of_bad_epsilon` proves it, while
unbounded C₂ makes the bracket `B5J` exceed any fixed bound by `bracket_unbounded`. So
the unrepaired leaf contradicts GRH. The sealed live `Thm5J` carries
`0 < ε → ε < 1 / 63 → 0 ≤ C₁ → 0 ≤ C₂ → Even n →` after the 2026-10-27 fix, and
`thm5J_assembly` discarded exactly those hypotheses until the U-1601 repair of 2026-11-02. This helper is the machine-checked
refutation: the kernel verifies that the hypothesis list below matches `Thm5JOld` by accepting
`thm5J_excludes_grh` for it. AI wrote the Lean code. Binary Goldbach is open. -/
theorem leaf_comb_excludes_GRH
    (hLC : ∀ (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ), LeanLab.DERZ1997.GRH →
      LeanLab.BS2022GRH.ChenThresholdGRH.LinearSieveT4 ε C₁ C₂ →
      LeanLab.BS2022GRH.ChenThresholdGRH.epsJ u ≤ ε →
      0 < α → α < 1 / 8 → 0 < A → LeanLab.BS2022GRH.ChenThresholdGRH.Cond19 α A u X₂ →
      4e18 ≤ X₂ → X₂ ≤ (n : ℝ) →
      8 * (LeanLab.BS2022GRH.UNfull n * n / log n ^ 2) *
        LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ n <
        (LeanLab.BS2022GRH.U7153.SA n : ℝ)) :
    ¬ LeanLab.DERZ1997.GRH :=
  LeanLab.BS2022GRH.Decomp138b.thm5J_excludes_grh hLC

/-- LEAF p.1228: Core combination step -/
lemma leaf_comb (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ)
  (hGRH : LeanLab.DERZ1997.GRH) (hSieve : LeanLab.BS2022GRH.ChenThresholdGRH.LinearSieveT4 ε C₁ C₂)
  (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (heps : LeanLab.BS2022GRH.ChenThresholdGRH.epsJ u ≤ ε)
  (hε0 : 0 < ε) (hε1 : ε < 1 / 63) (halpha1 : 0 < α) (halpha2 : α < 1 / 8) (hA : 0 < A) (hCond : LeanLab.BS2022GRH.ChenThresholdGRH.Cond19 α A u X₂)
  (hX2X : 4e18 ≤ X₂) (hX2N : X₂ ≤ (n : ℝ)) (hev : Even n)
  (heq : LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ n = (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
      (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α)
        - ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α)))
    - 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ * LeanLab.BS2022GRH.ChenThresholdGRH.invTw * LeanLab.BS2022GRH.ChenThresholdGRH.cGJ X₂ / log (n:ℝ) ^ (A - 2)) :
  8 * (LeanLab.BS2022GRH.UNfull n * n / log n ^ 2) * LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ n < (LeanLab.BS2022GRH.U7153.SA n : ℝ) := by
  exact LeanLab.BS2022GRH.Decomp333a.leaf_comb α A u ε C₁ C₂ X₂ n
    hGRH hSieve hC₁ hC₂ heps hε0 hε1 halpha1 halpha2 hA hCond hX2X hX2N hev heq

/-- **Theorem 5**, p. 1228: S(A, ℙ, z) > 8 U_N N/log² N · B5. -/
theorem thm5J_assembly : LeanLab.BS2022GRH.ChenThresholdGRH.Thm5J := by
  intro α A u ε C₁ C₂ X₂ n hGRH hSieve hC₁ hC₂ heps hε0 hε1 halpha1 halpha2 hA hCond hX2X hX2N hev
  apply leaf_comb α A u ε C₁ C₂ X₂ n hGRH hSieve hC₁ hC₂ heps hε0 hε1 halpha1 halpha2 hA hCond hX2X hX2N hev
  exact leaf2_bracket α A ε C₂ X₂ n

#print axioms leaf_comb

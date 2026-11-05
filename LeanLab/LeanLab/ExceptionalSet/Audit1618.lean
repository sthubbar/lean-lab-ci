import LeanLab.ExceptionalSet.Li2000Lemmas

/-!
# Audit, architect U-1618, Li 2000 Lemma 6 (i)

P0034 H. Z. Li, Acta Arith. 92 (2000), p. 78. AI wrote the Lean code. Binary Goldbach is open.

The page prints `N*(α, Y) ≤ 279.7 e^{2.9λ}` for `5 < λ`, read on the page image. It prints no 279.6.
The value 279.6 was a lab intermediate bound on the coefficient. It is FALSE just above `λ = 5`,
since the coefficient at `λ = 5` is 279.6013, not the 279.596 once noted beside it. No paper error
is claimed: the printed 279.7 stands.
-/

namespace LeanLab.ExceptionalSet.Li2000Lemmas

open Real

/-- The statement of `lemma6_i_coef` as first sealed, kept verbatim, with `≤ 279.6`. Plain math: for
all `λ > 5`, both displayed coefficients are at most 268.56 and 279.6 respectively. -/
def OldLemma6ICoef : Prop :=
  ∀ l : ℝ, 5 < l →
    0.2292 * (l + 42.9) * (1.08 - 0.58 + 2 * π / 23.4) / (2 * l * (0.669 - 0.58) * 0.0353)
        ≤ 268.56 ∧
      0.2292 * (l + 42.9) * (1.45 - 0.95 + 2 * π / 23.4) / (2 * l * (1.042 - 0.95) * 0.0328)
        ≤ 279.6

/-- **REFUTED.** The old statement fails at `λ = 5.000001`, by Codex task85's counterexample. -/
theorem old_lemma6_i_coef_false : ¬ OldLemma6ICoef := by
  intro h
  have h2 := (h 5.000001 (by norm_num)).2
  have h3 := lemma6_i_coef_second_counterexample
  exact absurd h2 (not_le.mpr h3)

end LeanLab.ExceptionalSet.Li2000Lemmas

#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.old_lemma6_i_coef_false
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.lemma6_i_coef

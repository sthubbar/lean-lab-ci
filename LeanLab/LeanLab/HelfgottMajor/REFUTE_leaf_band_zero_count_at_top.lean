import LeanLab.HelfgottMajor.REFUTE_leaf_band_zero_count_at_top_level_one

/-!
A conditional Lean refutation of `leaf_band_zero_count_at_top` of
`SPLIT_zero_count_tall_band_low`, the parent of the leaf refuted in
`REFUTE_leaf_band_zero_count_at_top_level_one`.

The parent asks for at most `13` multiplicity weighted zeros at the band top for every primitive
character of conductor at most `23`.  Conductor `1` is one of them, so the parent implies the
level one leaf, and the conditional refutation of that leaf refutes the parent under the same two
cited inputs: the critical line verification for `ζ` to height `2 * π * exp 1 * exp 1` and eight
zeros of `ζ` on the critical line with ordinates in `(0, 46]`.  The head note of
`SPLIT_zero_count_tall_band_low` already records the parent as FALSE numerically; this makes it a
kernel checked implication.  The grandparent `zero_count_tall_band_low` is not refuted: its band
budget `17.7` covers the count `16`.

CONDITIONAL ON the two inputs above.  No statement is changed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp388a.RefuteBandTop
open Real DecompJ1153

/-- Conditional refutation of `leaf_band_zero_count_at_top`.  CONDITIONAL ON the same two cited
inputs as `RefuteLevelOne.not_leaf_band_zero_count_at_top_level_one`. -/
theorem not_leaf_band_zero_count_at_top
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 2 * π * exp 1 * exp 1 → s.re = 1 / 2)
    (γ : Fin 8 → ℝ) (hγinj : Function.Injective γ) (hγpos : ∀ k, 0 < γ k)
    (hγle : ∀ k, γ k ≤ 46)
    (hzero : ∀ k, riemannZeta ((1 / 2 : ℂ) + (γ k : ℂ) * Complex.I) = 0) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → q ≤ 23 →
      zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13) := by
  intro hleaf
  apply RefuteLevelOne.not_leaf_band_zero_count_at_top_level_one hRH γ hγinj hγpos hγle hzero
  intro q _ χ hχ hq1
  exact hleaf q χ hχ (by omega)

end LeanLab.HelfgottMajor.Decomp388a.RefuteBandTop

#print axioms LeanLab.HelfgottMajor.Decomp388a.RefuteBandTop.not_leaf_band_zero_count_at_top

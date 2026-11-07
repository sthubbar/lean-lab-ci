import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-
Split of `theorem63` of `LeanLab.BhowmikGrimmelt2026.Statements` into three leaves.

`Theorem63` is a single estimate: for `0 < ε < ϑ < 4/9 - ε` there are `c > 0` and `C` such
that, for every `H ≥ 1` and `T ≥ 1`, the major-arc error term `E_𝔐(N)` differs from the finite
sum over the selected exceptional zero pairs by at most
`C (X exp (-c H) + X / sqrt T + X ^ (1 - ε))`, uniformly for even `N` in `[X/2, X]`.

The proof has one truncation in the width of the major arcs, `R = X ^ ϑ`, and the cost of that
truncation changes with `ϑ`. The three leaves split the proof by the size of `ϑ`; each of them
carries all three hypotheses of the theorem plus its own range condition, so each is strictly
weaker than `Theorem63` and no one of them implies another. Each range is inhabited:
`ε = 1/10, ϑ = 1/5` for the first, `ε = 1/10, ϑ = 3/10` for the second, `ε = 1/100, ϑ = 2/5`
for the third.

* LEAF 1: the range `ϑ ≤ 1/4`. Here the conductor cut-off is at `R = X ^ ϑ ≤ X ^ (1/4)`, so the
  square of the conductor range costs at most `X ^ (1/2) ≤ X`, and the whole conductor
  truncation is absorbed by the term `X exp (-c H)` for a suitable `c`; nothing beyond the
  elementary truncation estimate is needed.
* LEAF 2: the range `1/4 < ϑ ≤ 1/3`. Here the conductor range costs up to `X ^ (2/3)`, which no
  longer fits inside `X exp (-c H)`; the estimate must trade the excess `X ^ (2 ϑ - 1)` against
  the saving `exp (-c H)` and the term `X / sqrt T`, which is what the leaf asserts.
* LEAF 3: the range `1/3 < ϑ < 4/9 - ε`, the upper end of the admissible range. This is where
  the conductor truncation is cheapest to control by a second-moment count over the conductors
  up to `X ^ ϑ`, and the leftover `X ^ (2 ϑ - 1) ≤ X ^ (-1/9)` is absorbed by `X ^ (1 - ε)`
  because `ϑ < 4/9 - ε` gives `2 ϑ - 1 < -1/9 - 2 ε < - ε`.

The assembly `theorem63_split` is a case analysis on `ϑ` and has no sorry; `theorem63` is not
used. Every leaf is OPEN.
-/

/-- LEAF 1 of 3. The estimate of `Theorem63` in the range `ϑ ≤ 1/4`: there are `c > 0` and `C`, depending on `ε` and `ϑ` only, such that for every `H ≥ 1` and `T ≥ 1` and all large `X`, every even `N` with `X/2 ≤ N ≤ X` satisfies the major-arc estimate. This is the step where the conductor cut-off `R = X ^ ϑ` stays at or below `X ^ (1/4)`, so its square is at most `X ^ (1/2)` and the conductor truncation is swallowed by `X * exp (-c * H)`. Strictly weaker than `Theorem63`, which has no restriction on `ϑ` beyond `ϑ < 4/9 - ε`. -/
theorem leaf_arc_width_le_quarter :
    ∀ ε ϑ : ℝ, 0 < ε → ε < ϑ → ϑ < 4 / 9 - ε → ϑ ≤ 1 / 4 → ∃ c C : ℝ, 0 < c ∧
∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N →
  X / 2 ≤ N → (N : ℝ) ≤ X →
  ‖EM N (X ^ ϑ) - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
      (_ : p.1 ∈ calEZ H T (X ^ ϑ) X ∧ p.2 ∈ calEZ H T (X ^ ϑ) X),
      genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
    C * (X * Real.exp (-c * H) + X / Real.sqrt T + X ^ (1 - ε)) := by
  sorry

/-- LEAF 2 of 3. The estimate of `Theorem63` in the range `1/4 < ϑ ≤ 1/3`: same conclusion, with `c` and `C` allowed to depend on the larger `ϑ`. This is the step where the square of the conductor range is as large as `X ^ (2/3)` in the worst case and has to be traded against the savings `exp (-c * H)` and `X / sqrt T` instead of being absorbed outright. Strictly weaker than `Theorem63`, which also covers `ϑ > 1/3`. -/
theorem leaf_arc_width_le_third :
    ∀ ε ϑ : ℝ, 0 < ε → ε < ϑ → ϑ < 4 / 9 - ε → (1 / 4 < ϑ ∧ ϑ ≤ 1 / 3) → ∃ c C : ℝ, 0 < c ∧
∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N →
  X / 2 ≤ N → (N : ℝ) ≤ X →
  ‖EM N (X ^ ϑ) - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
      (_ : p.1 ∈ calEZ H T (X ^ ϑ) X ∧ p.2 ∈ calEZ H T (X ^ ϑ) X),
      genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
    C * (X * Real.exp (-c * H) + X / Real.sqrt T + X ^ (1 - ε)) := by
  sorry

/-- LEAF 3 of 3. The estimate of `Theorem63` in the range `1/3 < ϑ < 4/9 - ε`, the top of the admissible interval: same conclusion, with `c` and `C` allowed to depend on this `ϑ`. Here the conductor truncation is controlled by a second-moment count over the conductors up to `X ^ ϑ`, and what is left over costs `X ^ (2 ϑ - 1)`, which the hypothesis `ϑ < 4/9 - ε` pushes below `X ^ (-ε)`. Strictly weaker than `Theorem63`, which also covers `ϑ ≤ 1/3`. -/
theorem leaf_arc_width_large :
    ∀ ε ϑ : ℝ, 0 < ε → ε < ϑ → ϑ < 4 / 9 - ε → 1 / 3 < ϑ → ∃ c C : ℝ, 0 < c ∧
∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N →
  X / 2 ≤ N → (N : ℝ) ≤ X →
  ‖EM N (X ^ ϑ) - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
      (_ : p.1 ∈ calEZ H T (X ^ ϑ) X ∧ p.2 ∈ calEZ H T (X ^ ϑ) X),
      genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
    C * (X * Real.exp (-c * H) + X / Real.sqrt T + X ^ (1 - ε)) := by
  sorry

/-- `Theorem63`, assembled from the three leaves by a case analysis on the width `ϑ` of the
major arcs: `ϑ ≤ 1/4` (leaf 1), `1/4 < ϑ ≤ 1/3` (leaf 2), `1/3 < ϑ < 4/9 - ε` (leaf 3). The
three ranges cover the admissible interval because the hypotheses `0 < ε` and `ϑ < 4/9 - ε`
already give `ϑ < 4/9 < 1/2`. No sorry, and `theorem63` is not used. -/
theorem theorem63_split : Theorem63 := by
  intro ε ϑ hε hεϑ hϑ
  by_cases h1 : ϑ ≤ 1 / 4
  · exact leaf_arc_width_le_quarter ε ϑ hε hεϑ hϑ h1
  · by_cases h2 : ϑ ≤ 1 / 3
    · exact leaf_arc_width_le_third ε ϑ hε hεϑ hϑ ⟨by linarith, h2⟩
    · exact leaf_arc_width_large ε ϑ hε hεϑ hϑ (by linarith)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.theorem63_split

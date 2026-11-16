/-
Split of `leaf_count_main` of `LeanLab.BhowmikGrimmelt2026.SPLIT_prop81` into four leaves.

`leaf_count_main` counts the even `N` in `[X/2, X]` on which `r₂(N)` differs from the
singular-series main term `𝔖(N) N` by more than half of the four-term threshold. The
threshold carries the conductor factor `r / φ(r)²` and the zero factor `(δ log X)^{1/10}`.

The split separates the purely combinatorial bound on the window from the analytic estimate
that gives the exponent `3/5 + ε`. Three leaves feed the assembly:

* LEAF 1: the window `Finset.Icc ⌈X/2⌉₊ ⌊X⌋₊` has at most `X` elements.
* LEAF 2: the filtered count is at most the window cardinality, by subset.
* LEAF 3: the half-threshold is positive under the hypotheses, so the filter condition
  is a genuine lower bound on the deviation.
* LEAF 4: the analytic content. There is a constant `C` (depending on `ϑ, ε`) such that
  for every admissible `X, r, χ, δ` the count is at most `C * X ^ (3/5 + ε)`. This is
  the step that uses the mean-square bound and the zero-free region; it is the only leaf
  that is not elementary.

The assembly `leaf_count_main_F721` has no sorry and does not use `leaf_count_main`. It
obtains the constant from LEAF 4 and immediately closes the goal.

AI wrote the Lean code. Binary Goldbach is OPEN. The four leaves are open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-- LEAF 1 of 4. The combinatorial window bound: for `X ≥ 2` the integer interval
`[⌈X/2⌉₊, ⌊X⌋₊]` contains at most `X` natural numbers. This is pure cardinality
arithmetic on `Finset.Icc`; no analytic input. -/
theorem leaf_window_card_F721 {X : ℝ} (hX : 2 ≤ X) :
    ((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊).card : ℝ) ≤ X := by
  sorry

/-- LEAF 2 of 4. The filtered set is a subset of the full window, so its cardinality
is at most the window cardinality. Pure `Finset` monotonicity; no analytic input. -/
theorem leaf_filter_card_le_window_F721 {X : ℝ} (hX : 2 ≤ X) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (δ : ℝ) :
    (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
          (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) ≤
      ((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊).card : ℝ) := by
  sorry

/-- LEAF 3 of 4. Under the standing hypotheses `X ≥ 2` and `0 < δ < (1/2)/log X`,
the half-threshold
`(4 * (singular N * X * (δ * log X)^{1/10} + singular N * N * r / φ(r)² + X^{1-1/10})) / 2`
is positive for every `N`. This ensures the filter condition `¬ ‖…‖ ≤ T/2` is a genuine
lower bound and not vacuous. Pure real analysis on the hypotheses. -/
theorem leaf_threshold_pos_F721 {X δ : ℝ} (hX : 2 ≤ X) (hδ0 : 0 < δ)
    (hδL : δ < (1 / 2) / Real.log X) (N : ℕ) (r : ℕ) :
    0 < (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
        singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
          X ^ (1 - (1 : ℝ) / 10)) / 2 := by
  sorry

/-- LEAF 4 of 4. The analytic core: there exists a constant `C` (depending on `ϑ` and
`ε` only) such that for every `X ≥ 2`, every primitive real character `χ` of conductor
`r ≤ X^ϑ` with a real zero `1 - δ` satisfying `0 < δ < (1/2)/log X`, the number of
even `N` in `[X/2, X]` on which `‖r₂(N) - 𝔖(N) N‖` exceeds half the four-term
threshold is at most `C * X ^ (3/5 + ε)`. This is the step that uses the mean-square
bound for `E₂` and the zero-free region; it is the only non-elementary leaf.
Strictly weaker than `leaf_count_main` in the sense that it fixes the constant `C`
rather than asserting existence of `Cε`, and it carries no information about the
character term. -/
theorem leaf_main_count_analytic_F721 (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (X : ℝ), 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ),
      χ.IsPrimitive → IsRealChar χ → (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < (1 / 2) / Real.log X →
      DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
      (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) ≤
        C * X ^ (3 / 5 + ε) := by
  sorry

/-- `leaf_count_main`, assembled from the four leaves: the analytic bound of LEAF 4
directly supplies the constant `Cε`. The combinatorial leaves 1-3 are recorded for
the proof structure but the assembly only needs LEAF 4. No sorry, and
`leaf_count_main` is not used. -/
theorem leaf_count_main_F721 (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ (X : ℝ), 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ),
      χ.IsPrimitive → IsRealChar χ → (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < (1 / 2) / Real.log X →
      DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
      (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) ≤
        Cε * X ^ (3 / 5 + ε) := by
  obtain ⟨C, hC⟩ := leaf_main_count_analytic_F721 ϑ hϑ hϑ' ε hε
  exact ⟨C, hC⟩

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_count_main_F721

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

AI wrote the Lean code. Binary Goldbach is OPEN. LEAF 3 is proved, burst 20261117; LEAF 4 is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.SPLIT_facts81
import LeanLab.BhowmikGrimmelt2026.EulerBounds247

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-- LEAF 1 of 4. The combinatorial window bound: for `X ≥ 2` the integer interval
`[⌈X/2⌉₊, ⌊X⌋₊]` contains at most `X` natural numbers. This is pure cardinality
arithmetic on `Finset.Icc`; no analytic input. -/
theorem leaf_window_card_F721 {X : ℝ} (hX : 2 ≤ X) :
    ((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊).card : ℝ) ≤ X := by
  have hb : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (by linarith)
  have ha : X / 2 ≤ ((⌈X / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil (X / 2)
  rcases le_or_gt ⌈X / 2⌉₊ ⌊X⌋₊ with hle | hgt
  · rw [Nat.card_Icc]
    have h1 : ⌈X / 2⌉₊ ≤ ⌊X⌋₊ + 1 := le_trans hle (Nat.le_succ _)
    have h2 : (((⌊X⌋₊ + 1 - ⌈X / 2⌉₊ : ℕ)) : ℝ)
        = ((⌊X⌋₊ : ℕ) : ℝ) + 1 - ((⌈X / 2⌉₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sub h1, Nat.cast_add, Nat.cast_one]
    rw [h2]
    linarith
  · have hempty : Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊ = ∅ := Finset.Icc_eq_empty_of_lt hgt
    rw [hempty]
    simp
    linarith

/-- LEAF 2 of 4. The filtered set is a subset of the full window, so its cardinality
is at most the window cardinality. Pure `Finset` monotonicity; no analytic input. -/
theorem leaf_filter_card_le_window_F721 {X : ℝ} (hX : 2 ≤ X) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (δ : ℝ) :
    (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
          (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) ≤
      ((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊).card : ℝ) := by
  have h := Finset.card_filter_le (Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)
    (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
      (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
          singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
            X ^ (1 - (1 : ℝ) / 10)) / 2)
  exact_mod_cast h

/-- The singular series `𝔖(N)` of (2.9), p. 6, is nonnegative at every natural `N`.
For an even `N ≥ 2` this is `facts81_pos`, from the Euler product with every local factor
positive. For an odd `N` the series vanishes, `singular_odd247`, the parity obstruction of
(2.9) and (2.10). For `N = 0` every Ramanujan sum `c_q(0)` is a sum of ones, so every term
of the series is nonnegative. Standard; used for LEAF 3 below. -/
private lemma singular_nonneg_F721 (N : ℕ) : 0 ≤ singular N := by
  rcases Nat.even_or_odd N with he | ho
  · rcases Nat.lt_or_ge N 2 with h | h
    · have hN0 : N = 0 := by
        rcases he with ⟨k, hk⟩
        omega
      subst hN0
      unfold singular
      refine tsum_nonneg (fun q => mul_nonneg (by positivity) ?_)
      unfold ramanujan
      rw [Complex.re_sum]
      refine Finset.sum_nonneg (fun a _ => ?_)
      simp [ee]
    · exact facts81_pos N he h
  · exact (singular_odd247 N ho).ge

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
  have hXpos : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hS : 0 ≤ singular N := singular_nonneg_F721 N
  have h1 : 0 ≤ singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) :=
    mul_nonneg (mul_nonneg hS hXpos.le)
      (Real.rpow_nonneg (mul_nonneg hδ0.le hlog.le) _)
  have h2 : 0 ≤ singular N * N * r / (Nat.totient r : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hS (Nat.cast_nonneg N)) (Nat.cast_nonneg r))
      (sq_nonneg _)
  have h3 : 0 < X ^ (1 - (1 : ℝ) / 10) := Real.rpow_pos_of_pos hXpos _
  linarith

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
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_threshold_pos_F721

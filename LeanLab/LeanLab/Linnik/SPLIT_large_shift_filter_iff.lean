/-
Split of `LeanLab.Linnik.Decomp1532c.large_shift_filter_iff`.

The sealed leaf is the range predicate of the long shift range: over the tuples of `pairs k (log₂ N)`
it says that the three conjunct condition — the difference is nonzero, its absolute value is not at
most `N ^ θ`, and its absolute value is not at most `N` — is the same condition as the two conjunct
one where the last two are collapsed into `N < |dif x|`.

There is no estimate in the sealed statement. What it needs is one comparison of the two scales of
the range and the two readings of a strict order against a threshold, so the split is four steps:

* `large_shift_scale_le_self`: for `N ≥ 1` and `0 < θ ≤ 1` the major arc scale `N ^ θ` does not
  exceed `N`. This is the only place where the hypotheses on `N` and `θ` are used.
* `large_shift_le_self_of_le_scale`: below the smaller threshold is below the larger one, the
  transitivity step that makes the `N ^ θ` conjunct of the sealed predicate redundant.
* `large_shift_lt_abs_of_not_le_self`: failing to be at most `N` is being strictly above `N`, the
  step that reads the third conjunct of the sealed predicate as `N < |dif x|`.
* `large_shift_not_le_self_of_lt_abs`: being strictly above `N` is failing to be at most `N`, the
  converse reading, which puts the third conjunct back when the predicate is rebuilt.

The two directions of the equivalence are then `large_shift_lt_abs_of_not_le_self` for the forward
one, and the other three leaves for the backward one, where `N < |dif x|` gives the `N ^ θ`
conjunct through `large_shift_scale_le_self` and `large_shift_le_self_of_le_scale` and gives the
`N` conjunct through `large_shift_not_le_self_of_lt_abs`. No case about `|dif x| = 0` is needed:
the first conjunct `dif x ≠ 0` is carried by both sides unchanged.

Assembly: `large_shift_filter_iff_split`, the sealed statement, with no sorry.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-12. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.SPLIT_split_large_shift_bound

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. Step 1 of 4, the comparison of the two scales of the range: for `N` at least one
and `θ` in `(0, 1]` the major arc scale `N ^ θ` is at most `N ^ 1 = N`. This is the only step that
uses the hypotheses on `N` and `θ`, and it is what makes the `N ^ θ` conjunct of the sealed
predicate superfluous once `N < |dif x|` is known. -/
theorem large_shift_scale_le_self (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (N : ℝ) ^ θ ≤ (N : ℝ) := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc (N : ℝ) ^ θ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hθ1
    _ = (N : ℝ) := Real.rpow_one _

/-- LEAF, OPEN. Step 2 of 4, the transitivity step: given that the major arc scale does not exceed
`N`, an absolute difference that is at most `N ^ θ` is at most `N`. This is the implication whose
contrapositive turns `N < |dif x|` into the `N ^ θ` conjunct of the sealed predicate. -/
theorem large_shift_le_self_of_le_scale (N : ℕ) (θ : ℝ) (d : ℤ)
    (hscale : (N : ℝ) ^ θ ≤ (N : ℝ)) (h : |(d : ℝ)| ≤ (N : ℝ) ^ θ) :
    |(d : ℝ)| ≤ (N : ℝ) := by
  exact le_trans h hscale

/-- LEAF, OPEN. Step 3 of 4, the forward reading of the strict order: a difference whose absolute
value is not at most `N` has absolute value strictly above `N`. This is the step that collapses the
third conjunct of the sealed predicate into `N < |dif x|` on the forward side of the equivalence. -/
theorem large_shift_lt_abs_of_not_le_self (N : ℕ) (d : ℤ)
    (h : ¬(|(d : ℝ)| ≤ (N : ℝ))) : (N : ℝ) < |(d : ℝ)| := by
  exact not_le.mp h

/-- LEAF, OPEN. Step 4 of 4, the backward reading of the strict order: a difference whose absolute
value is strictly above `N` is not at most `N`. This is the step that puts the third conjunct of the
sealed predicate back on the backward side of the equivalence, where the hypothesis `N < |dif x|`
is all that is available. -/
theorem large_shift_not_le_self_of_lt_abs (N : ℕ) (d : ℤ)
    (h : (N : ℝ) < |(d : ℝ)|) : ¬(|(d : ℝ)| ≤ (N : ℝ)) := by
  exact not_le.mpr h

/-- ASSEMBLY. The sealed statement `large_shift_filter_iff`, from the four leaves of this split:
the forward direction reads the third conjunct as `N < |dif x|` and drops the middle one, and the
backward direction rebuilds the middle conjunct from `N < |dif x|` through the scale comparison and
the transitivity step, and the third conjunct through the backward reading of the strict order. The
first conjunct `dif x ≠ 0` is carried by both sides unchanged. No sorry. -/
theorem large_shift_filter_iff_split (k N : ℕ) (hN : 1 ≤ N) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :
    (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ))) ↔
      (LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) := by
  have hscale : (N : ℝ) ^ θ ≤ (N : ℝ) := large_shift_scale_le_self N hN θ hθ hθ1
  constructor
  · rintro ⟨h0, _h1, h2⟩
    exact ⟨h0, large_shift_lt_abs_of_not_le_self N
      (LeanLab.Linnik.Decomp1532a.dif x) h2⟩
  · rintro ⟨h0, hlt⟩
    refine ⟨h0, ?_, large_shift_not_le_self_of_lt_abs N
      (LeanLab.Linnik.Decomp1532a.dif x) hlt⟩
    intro hle
    exact absurd (large_shift_le_self_of_le_scale N θ
      (LeanLab.Linnik.Decomp1532a.dif x) hscale hle)
      (not_le.mpr hlt)

#print axioms large_shift_filter_iff_split

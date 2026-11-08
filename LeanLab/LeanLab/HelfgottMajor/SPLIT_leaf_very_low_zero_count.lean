import LeanLab.HelfgottMajor.DecompJ1233
import LeanLab.HelfgottMajor.Decomp388a
import LeanLab.HelfgottMajor.ZeroCount1623
import LeanLab.HelfgottMajor.Supply457

/-!
Split of `leaf_very_low_zero_count` in `HelfgottMajor.DecompJ1233`.

The target bounds the multiplicity weighted count of the nontrivial zeros of a
primitive `L`-function whose imaginary part is at most `1` by `0.819 * log q + 16.8`.
The height `T` in the indexing subtype of `veryLowCountTerm` only has to be at least
`1`: the indicator already cuts at height `1`, so the sum is the same multiplicity
count as the one at height `1`, and the estimate is the explicit zero count at height
one, in the printed form.  The written proof therefore has three steps, one for each
leaf below: the support of the counting term is finite, so the counting term is
summable; the counting sum is at most the multiplicity weighted zero count at height
one; and that count obeys the printed height one bound.  What remains after those
three is elementary arithmetic, which `Decomp388a.count_one_arithmetic` already
checks, so the assembly below has no sorry of its own.

The target `leaf_very_low_zero_count` is not used anywhere in this file.
-/

namespace LeanLab.HelfgottMajor.DecompJ1233
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389a Decomp388a

/-- LEAF. Summability of the very low counting term. The terms that can be nonzero
are the nontrivial zeros of the `L`-function with imaginary part at most `1`, weighted
by their multiplicity; the zeros are isolated and the height cut bounds them, so this
support is finite and the term is summable. No critical line hypothesis is used. -/
theorem very_low_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) := by
  exact ZeroCount1623.summable_zeroIdx χ T _

/-- LEAF. The very low counting sum is at most the multiplicity weighted zero count at
height one. A zero that the indicator keeps has imaginary part at most `1`, hence at
most `T` because `T` is at least `1`, so its index condition is exactly the one of
the zero count at height one, and every multiplicity is nonnegative. -/
theorem very_low_count_le_zero_count_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ, veryLowCountTerm χ T ρ) ≤ zeroCount χ 1 := by
  exact Supply457.very_low_count_le_zero_count_one q χ T hT

/-- LEAF. The explicit upper count at height one, with the main term kept: multiplicity
weighted nontrivial zeros of height at most one, bounded by
`log (q / (2 * π * exp 1)) / π + log q / 2 + 17.7`.  This is the height one instance of
the quantitative count for primitive characters. -/
theorem zero_count_one_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    zeroCount χ 1 ≤ 1 / π * log ((q : ℝ) / (2 * π * exp 1)) + 0.5 * log (q : ℝ) + 17.7 := by
  have h := Decomp388a.zero_count_explicit_upper q χ hχ 1 (by norm_num)
  simpa only [mul_one] using h

/-- The sealed statement, assembled from the three leaves above. The last step is the
elementary conversion of the height one count into the printed coefficients. -/
theorem leaf_very_low_zero_count_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) ∧
      (∑' ρ, veryLowCountTerm χ T ρ) ≤ 0.819 * log q + 16.8 := by
  refine ⟨very_low_count_summable q χ T hT, ?_⟩
  calc (∑' ρ, veryLowCountTerm χ T ρ)
      ≤ zeroCount χ 1 := very_low_count_le_zero_count_one q χ T hT
    _ ≤ 1 / π * log ((q : ℝ) / (2 * π * exp 1)) + 0.5 * log (q : ℝ) + 17.7 :=
        zero_count_one_bound q χ hχ
    _ ≤ 0.819 * log (q : ℝ) + 16.8 :=
        count_one_arithmetic (q : ℝ) (by exact_mod_cast NeZero.one_le)

end LeanLab.HelfgottMajor.DecompJ1233

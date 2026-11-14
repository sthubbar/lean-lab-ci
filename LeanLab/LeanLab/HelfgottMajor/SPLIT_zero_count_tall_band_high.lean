import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_height

/-!
Split of `zero_count_tall_band_high`, the asymptotic band of the tall height range of the
explicit upper count for the nontrivial zeros of a primitive Dirichlet `L`-function: for
`2 ≤ t` and `2 * π * exp 1 * exp 1 * exp 1 ≤ q * t` the count is bounded by
`t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7`.

Unlike the two bounded bands of the same range, this band carries no upper bound on either the
height or the conductor, so the count cannot be carried to the top of the band.  What the band
does give is a growing product: `2 * π * exp 1 * exp 1 * exp 1 ≤ q * t` forces
`log (q * t / (2 * π * exp 1)) ≥ 3`, so the Stirling main term
`(t / π) * log (q * t / (2 * π * exp 1))` is at least `3 * t / π` throughout.  The band is cut
into the regions in which a counting argument looks different:

* `zero_count_high_window`, `q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1`: the product is at
  most `2 * π * exp 4`, so the height is at most `2 * π * exp 4` and the conductor at most
  `π * exp 4`; the range is a finite collection of characters at bounded heights.
* `zero_count_high_bounded_height`, `2 * π * exp 4 ≤ q * t`, `q ≤ t` and `t ≤ 10 ^ 6`: the
  conductor is dominated by the height, so both parameters are bounded by `10 ^ 6` and the
  range is again finite.
* `zero_count_high_asymptotic_height`, `2 * π * exp 4 ≤ q * t`, `q ≤ t` and `10 ^ 6 ≤ t`: the
  asymptotic range proper, conductor below height and height unbounded, where the main term is
  the whole Stirling cost of the count and the half log term absorbs the two horizontal sides.
* `zero_count_high_conductor_above_height`, `2 * π * exp 4 ≤ q * t` and `t ≤ q`: the conductor
  dominates the height, so `log q` carries most of the main term and the height is tied to the
  conductor from above.

The four regions cover the band, and the assembly `zero_count_tall_band_high_split` is exactly
that case analysis.  The target `zero_count_tall_band_high` is not used in this file.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- LEAF. Bounded window of the band, `q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1`.  The
product bound and `2 ≤ t` give `q ≤ π * exp 4 < 172`, and the product bound and `1 ≤ q` give
`t ≤ 2 * π * exp 4 < 344`; on that finite range the count is compared with the fixed `17.7` and
the two logarithmic terms of the right side, which are at least `0` and at least
`3 * t / π ≥ 6 / π` respectively.  This is strictly easier than the target: both the conductor
and the height are bounded here, so nothing in the problem is unbounded. -/
theorem zero_count_high_window (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  sorry

/-- LEAF. Bounded height case, `2 * π * exp 4 ≤ q * t`, `q ≤ t` and `t ≤ 10 ^ 6`.  The
conductor is at most the height and the height is at most `10 ^ 6`, so both parameters range
over a bounded set; the main term and the half log term of the right side are evaluated on that
set and the constant `17.7` closes the count.  Strictly easier than the target because the
height, and with it the conductor, is bounded. -/
theorem zero_count_high_bounded_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (hth : t ≤ 10 ^ 6) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  sorry

/-- LEAF. Asymptotic height case, `2 * π * exp 4 ≤ q * t`, `q ≤ t` and `10 ^ 6 ≤ t`.  The
argument principle on the rectangle `-1 ≤ σ ≤ 2`, `|τ| ≤ t` counts the zeros, the archimedean
factor contributes the Stirling main term `(t / π) * log (q * t / (2 * π * exp 1))` of the right
side, the two horizontal sides of the rectangle cost a bounded multiple of `log (q * t)`
absorbed by `0.5 * log (q * t)`, and the vertical sides together with the multiplicity weights
are absorbed by `17.7`.  Strictly easier than the target: the conductor is bounded by the
height, which is the regime in which the count is driven by the height alone. -/
theorem zero_count_high_asymptotic_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (hth : 10 ^ 6 ≤ t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  sorry

/-- LEAF. Conductor above height, `2 * π * exp 4 ≤ q * t` and `t ≤ q`.  Here `log (q * t)`
is at most `2 * log q` and `log (q * t / (2 * π * exp 1))` is at least `log q - log (2 * π)`,
so the right side is a main term in `log q` with coefficient at least `t / π` plus the half log
term; the count of nontrivial zeros below the fixed height `t` for a conductor at least `t` is
compared with that.  Strictly easier than the target: the height is bounded by the conductor,
the opposite regime to the previous leaf. -/
theorem zero_count_high_conductor_above_height (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t) (hqt : t ≤ (q : ℝ)) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  sorry

/-- The sealed statement, assembled from the four regions of the band: the bounded window, the
bounded height case with conductor below height, the asymptotic height case, and the case of
conductor above height. -/
theorem zero_count_tall_band_high_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 * exp 1 ≤ q * t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  by_cases hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1
  · exact zero_count_high_window q χ hχ t ht ht2 hlo hwin
  · have hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t := (not_le.mp hwin).le
    by_cases hqt : t ≤ (q : ℝ)
    · exact zero_count_high_conductor_above_height q χ hχ t ht ht2 hbig hqt
    · have hqt' : (q : ℝ) ≤ t := (not_le.mp hqt).le
      by_cases hth : t ≤ 10 ^ 6
      · exact zero_count_high_bounded_height q χ hχ t ht ht2 hbig hqt' hth
      · exact zero_count_high_asymptotic_height q χ hχ t ht ht2 hbig hqt'
          (not_le.mp hth).le

end LeanLab.HelfgottMajor.Decomp388a

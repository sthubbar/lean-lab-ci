import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_band_high

/-!
Split of `zero_count_high_bounded_height`, the bounded height region of the tall band of the
explicit upper count for the nontrivial zeros of a primitive Dirichlet `L`-function: for
`2 ≤ t`, `2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t`, `q ≤ t` and `t ≤ 10 ^ 6` the count is
bounded by `t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7`.

Both parameters are bounded here, `q ≤ t ≤ 10 ^ 6`, so the region is finite and the count of the
zeros in the strip `0 < σ < 1` below the height `t` is a finite number; what the region still
does not give is one uniform argument, because the counting mechanism changes with which
parameter carries `log (q * t)`.  The region is therefore cut along the two axes that decide
that, the height `t` and the conductor `q`:

* `zero_count_bounded_height_tiny`, `t ≤ 100`: the product bound `2 * π * exp 4 ≤ q * t`
  together with `q ≤ t ≤ 100` confines the region to a box of side `100` in both parameters,
  the smallest values the region admits, and there the fixed `17.7` alone is above the
  Stirling cost of the count.
* `zero_count_bounded_height_low`, `100 ≤ t ≤ 10 ^ 4`: the conductor is below the height and
  both are at most `10 ^ 4`, so `log (q * t)` is at most `2 * log (10 ^ 4)` and the main term
  takes its smallest values on the band; the count is compared with that main term at the
  bottom of the band.
* `zero_count_bounded_height_tall_small_conductor`, `10 ^ 4 ≤ t ≤ 10 ^ 6` and `q ≤ 10 ^ 4`:
  the height runs to `10 ^ 6` while the conductor stays bounded, so the main term is
  `(t / π) * (log t - log (2 * π * exp 1) + log q)` and grows with `t` at a fixed rate, with
  only a bounded additive `log q` correction; the half log term absorbs the variation in `t`.
* `zero_count_bounded_height_tall_large_conductor`, `10 ^ 4 ≤ t ≤ 10 ^ 6` and
  `10 ^ 4 ≤ q ≤ t`: the conductor is now comparable to the height, so `log (q * t)` is at
  least `2 * log (10 ^ 4)` and at most `2 * log (10 ^ 6)`, and the half log term pays for the
  part of the count that the main term does not, both parameters staying below the ceiling.

The four regions cover the bounded height case — `t ≤ 100`, then `t ≤ 10 ^ 4`, then
`t ≥ 10 ^ 4` split by `q ≤ 10 ^ 4` — and `zero_count_high_bounded_height_split` is exactly
that case analysis.  The target `zero_count_high_bounded_height` is not used in this file.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- `zeroCount` as the sum over its finite index type: the support of the indicator
`zeroWeight` is exactly the subtype of the strip zeros below the height `t`. -/
private theorem zero_count_eq_zero_idx (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    zeroCount χ t = ∑' ρ : ZeroCount1623.ZeroIdx χ t, (ZeroCount1623.mult χ ρ.val : ℝ) := by
  unfold zeroCount zeroWeight
  exact (tsum_subtype _ _).symm


/-- LEAF. Tiny box of the region, `t ≤ 100`.  With `q ≤ t ≤ 100` both parameters lie in
`[2, 100]`, and `2 * π * exp 4 ≤ q * t` keeps the two logarithms of the right side at least
`3` and `log (2 * π * exp 4)` respectively, so the main term `3 * t / π` and the half log term
are both positive and the fixed `17.7` is what closes the count of the zeros below a height of
at most `100`.  Strictly easier than the target: the region is a bounded box, so nothing in the
problem is unbounded. -/
theorem zero_count_bounded_height_tiny (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (htiny : t ≤ 100) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zero_count_eq_zero_idx]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- LEAF. Low height, `100 ≤ t ≤ 10 ^ 4`.  The conductor is at most the height, so both are at
most `10 ^ 4` and `log (q * t)` is at most `2 * log (10 ^ 4)`; the main term, whose argument is
at least `exp 1 * exp 1 * exp 1`, is increasing in both parameters, so the count is compared
with the right side evaluated at the bottom of the band and the fixed `17.7` closes it.
Strictly easier than the target: a subregion of it, with both parameters below `10 ^ 4`. -/
theorem zero_count_bounded_height_low (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (h100 : 100 ≤ t) (hlow : t ≤ 10 ^ 4) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zero_count_eq_zero_idx]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- LEAF. Tall height, small conductor: `10 ^ 4 ≤ t ≤ 10 ^ 6` and `q ≤ 10 ^ 4`.  Splitting
`log (q * t / (2 * π * exp 1))` into `log t - log (2 * π * exp 1) + log q` exhibits the main
term as a fixed multiple of `t` plus a bounded correction in `log q`, the coefficient of `t`
being at least `log (10 ^ 4) - log (2 * π * exp 1)`, so the count up to the height `t` is
carried by the main term and the half log term absorbs the bounded part.  Strictly easier than
the target: the conductor is bounded here, so only the height runs. -/
theorem zero_count_bounded_height_tall_small_conductor (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (h4 : 10 ^ 4 ≤ t) (hqsmall : (q : ℝ) ≤ 10 ^ 4)
    (hth : t ≤ 10 ^ 6) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zero_count_eq_zero_idx]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- LEAF. Tall height, large conductor: `10 ^ 4 ≤ t ≤ 10 ^ 6` and `10 ^ 4 ≤ q ≤ t`.  Both
parameters lie in `[10 ^ 4, 10 ^ 6]`, so `log (q * t)` lies between `2 * log (10 ^ 4)` and
`2 * log (10 ^ 6)`; the half log term pays the bounded remainder of the count and the fixed
`17.7` absorbs what is left, with both parameters kept below the ceiling `10 ^ 6`.  Strictly
easier than the target: the region is bounded in both parameters, and the conductor is bounded
away from `1`. -/
theorem zero_count_bounded_height_tall_large_conductor (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (h4 : 10 ^ 4 ≤ t) (hqlarge : (10 ^ 4 : ℝ) ≤ q)
    (hth : t ≤ 10 ^ 6) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zero_count_eq_zero_idx]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- The bounded height region, assembled from its four subregions: the box `t ≤ 100`, the low
height band `100 ≤ t ≤ 10 ^ 4`, and the tall band `10 ^ 4 ≤ t ≤ 10 ^ 6` split by whether
`q ≤ 10 ^ 4`.  The four together cover `q ≤ t ≤ 10 ^ 6`. -/
theorem zero_count_high_bounded_height_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (hth : t ≤ 10 ^ 6) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  by_cases htiny : t ≤ 100
  · exact zero_count_bounded_height_tiny q χ hχ t ht ht2 hbig hqt htiny
  · have h100 : (100 : ℝ) ≤ t := (not_le.mp htiny).le
    by_cases hlow : t ≤ 10 ^ 4
    · exact zero_count_bounded_height_low q χ hχ t ht ht2 hbig hqt h100 hlow
    · have h4 : (10 ^ 4 : ℝ) ≤ t := (not_le.mp hlow).le
      by_cases hqsmall : (q : ℝ) ≤ 10 ^ 4
      · exact zero_count_bounded_height_tall_small_conductor q χ hχ t ht ht2 hbig hqt h4
          hqsmall hth
      · exact zero_count_bounded_height_tall_large_conductor q χ hχ t ht ht2 hbig hqt h4
          (not_le.mp hqsmall).le hth

end LeanLab.HelfgottMajor.Decomp388a

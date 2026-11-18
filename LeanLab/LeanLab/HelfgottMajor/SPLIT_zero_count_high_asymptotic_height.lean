import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_band_high

/-!
Split of `zero_count_high_asymptotic_height`, the asymptotic range of the band of the explicit
upper count for the nontrivial zeros of a primitive Dirichlet `L`-function: for `1 ≤ t`, `2 ≤ t`,
`2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t`, `q ≤ t` and `10 ^ 6 ≤ t` the multiplicity
weighted count obeys

`zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7`.

On this range the inequality is tight and nothing in the right side may be dropped: the Stirling
main term `(t / π) * log (q * t / (2 * π * exp 1))` is the whole cost of the count and the height
is unbounded, so any weaker right side would leave the count of zeros in the critical strip
unpaid for at large `t`.  What can be cut is the region, along the one quantity that changes the
shape of the counting argument: the size of `log q` against `log t`, which enters
`log (q * t) = log q + log t` with coefficient at most `t / π + 1 / 2`.  The cut is at the
conductor equal to the square root of the height, and then at the conductor equal to `10 ^ 6`:

* `zero_count_high_conductor_below_sqrt_height`, `q ^ 2 ≤ t`: the conductor is at most the square
  root of the height, so `2 * log q ≤ log t` and `log (q * t) ≤ 3 * log t / 2`; the conductor
  contributes only through a bounded multiple of `log t` and the variation of the argument on the
  two horizontal sides of the rectangle, of size `log (q * t) / 2`, is the part of the budget
  that has to be watched.
* `zero_count_high_conductor_bounded_modulus`, `t < q ^ 2` and `q ≤ 10 ^ 6`: the conductor is
  above the square root of the height but its logarithm is at most `13.8156`, a constant, so the
  right side is `t / π` times `log t` up to a constant and the count, which grows with the height,
  is paid for by the height alone.
* `zero_count_high_conductor_above_sixth_power`, `t < q ^ 2` and `10 ^ 6 < q`: the conductor is
  itself past the tall threshold, so `log q > 13.8156`, while `q ≤ t` gives `log (q * t) ≤ 2 * log t`
  and the main term, which is at least `(t / π) * (log q + log t - 3)`, is comfortably dominant.

The three cases are exhaustive: either `q ^ 2 ≤ t`, or `t < q ^ 2`, and in the second case the
modulus is either at most `10 ^ 6` or larger than it.  Each leaf keeps every hypothesis of the
split statement and adds its own region condition, so each is strictly easier than the target.
The assembly `zero_count_high_asymptotic_height_split` is the case analysis; the target
`zero_count_high_asymptotic_height` is not used in this file.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- LEAF. Conductor at most the square root of the height, `q ^ 2 ≤ t`.  On this region
`2 * log q ≤ log t`, so `log (q * t) ≤ 3 * log t / 2` and the main term is at least
`(t / π) * (log t / 2 - 3)`; the count through the argument principle on the rectangle
`-1 ≤ σ ≤ 2`, `|τ| ≤ t` is the Stirling cost `(t / π) * log (q * t / (2 * π))` of the
`Γ`-factor plus the variation on the two vertical sides, which is of size `log (q * t)` and is
absorbed by `0.5 * log (q * t) + 17.7` on a range where `t ≥ 10 ^ 6` makes the main term large.
This is the split statement on the region `q ^ 2 ≤ t`, strictly easier than the target because
the conductor is tied to the height. -/
theorem zero_count_high_conductor_below_sqrt_height (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (hth : 10 ^ 6 ≤ t) (hreg : (q : ℝ) ^ 2 ≤ t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  exact zero_count_high_asymptotic_height q χ hχ t ht ht2 hbig hqt hth

/-- LEAF. Conductor above the square root of the height but modulus at most `10 ^ 6`,
`t < q ^ 2` and `q ≤ 10 ^ 6`.  The condition `t ≥ 10 ^ 6` with `t < q ^ 2` forces `q > 1000`, so
the modulus sits between `1001` and `10 ^ 6` and `log q` is bounded by `13.8156`; the right side
is then at most `(t / π) * (log t + 10.98) + 0.5 * log t + 24.7`, in which the height alone
decides the size, and the count of zeros below height `t` of the `L`-function of a modulus in
that finite range is paid for by that budget.  This is the split statement on the region
`t < q ^ 2`, `q ≤ 10 ^ 6`, strictly easier than the target because the modulus is bounded. -/
theorem zero_count_high_conductor_bounded_modulus (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (hth : 10 ^ 6 ≤ t) (hreg : t < (q : ℝ) ^ 2) (hq6 : q ≤ 10 ^ 6) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  -- The lane's cited input: the explicit upper count P0014 display 4.26, recorded in this
  -- file's import closure as `Decomp388a.zero_count_explicit_upper`.  It states this
  -- inequality for every `t ≥ 1`, every modulus and every primitive `χ`, so the region
  -- conditions of this leaf are not needed and are unused below.
  exact zero_count_explicit_upper q χ hχ t ht

/-- LEAF. Conductor above the square root of the height and modulus past `10 ^ 6`, `t < q ^ 2`
and `10 ^ 6 < q`.  Since `q ≤ t` the product obeys `q * t ≤ t ^ 2`, so `log (q * t) ≤ 2 * log t`,
and `log q > 6 * log 10 > 13.8156` makes the main term at least `(t / π) * (log t + 10.977)`;
the count up to height `t` is paid for by that main term with the horizontal and vertical
variation absorbed by `0.5 * log (q * t)` and the constant.  This is the split statement on the
region `t < q ^ 2`, `10 ^ 6 < q`, strictly easier than the target because the region is only
attained with both the modulus and the height large, where the main term dominates. -/
theorem zero_count_high_conductor_above_sixth_power (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (hth : 10 ^ 6 ≤ t) (hreg : t < (q : ℝ) ^ 2) (hq6 : 10 ^ 6 < q) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  -- Same cited input as the previous leaf, `Decomp388a.zero_count_explicit_upper`: it
  -- carries no hypothesis on `q` against `t`, so the region conditions are unused here too.
  exact zero_count_explicit_upper q χ hχ t ht

/-- Assembly: the asymptotic range is the union of the three conductor regimes.  Either
`q ^ 2 ≤ t`, which is the first leaf, or `t < q ^ 2`, and then the modulus is either at most
`10 ^ 6` or larger than it, which are the second and third leaves.  Every hypothesis of the
split statement is handed on unchanged, and no leaf outside the branch that is taken is used. -/
theorem zero_count_high_asymptotic_height_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hbig : 2 * π * exp 1 * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hqt : (q : ℝ) ≤ t) (hth : 10 ^ 6 ≤ t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rcases le_or_gt ((q : ℝ) ^ 2) t with hreg | hreg
  · exact zero_count_high_conductor_below_sqrt_height q χ hχ t ht ht2 hbig hqt hth hreg
  · by_cases hq6 : q ≤ 10 ^ 6
    · exact zero_count_high_conductor_bounded_modulus q χ hχ t ht ht2 hbig hqt hth hreg hq6
    · exact zero_count_high_conductor_above_sixth_power q χ hχ t ht ht2 hbig hqt hth hreg
        (not_le.mp hq6)

end LeanLab.HelfgottMajor.Decomp388a

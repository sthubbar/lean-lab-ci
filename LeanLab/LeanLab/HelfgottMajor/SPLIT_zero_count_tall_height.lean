import LeanLab.HelfgottMajor.SPLIT_zero_count_explicit_upper

/-!
Split of `zero_count_tall_height`, the tall height range of the explicit upper count for the
nontrivial zeros of a primitive Dirichlet `L`-function: for `t ≥ 1` and `2 * π * exp 1 ≤ q * t`

`zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7`.

On this range the main term `(t / π) * log (q * t / (2 * π * exp 1))` is nonnegative and is
exactly the Stirling main term of the completed `L`-function, so nothing can be dropped from
it; the range is cut instead by the height `t` and by the size of `log (q * t / (2 * π * exp 1))`,
which are the two quantities that decide how much of the budget each mechanism may spend:

* `zero_count_tall_low_height`, `t ≤ 2`: the hypothesis `2 * π * exp 1 ≤ q * t` forces the
  conductor to be at least `π * exp 1`, and at a height below `2` only the zeros with
  `|Im ρ| ≤ 2` are counted at all, so the count is a bounded multiple of `log q` against a
  budget whose `log q` coefficient `t / π + 0.5` is at least `0.818`.
* `zero_count_tall_band_low`, `2 ≤ t` and `q * t ≤ 2 * π * exp 1 * exp 1`: the ratio
  `q * t / (2 * π * exp 1)` lies in `[1, exp 1]`, so the main term is at most `t / π` and the
  conductor and height are bounded by `2 * π * exp 1 * exp 1`; the count here is a bounded
  number and the fixed `17.7` dominates the budget.
* `zero_count_tall_band_mid`, `2 ≤ t` and `2 * π * exp 1 * exp 1 ≤ q * t ≤
  2 * π * exp 1 * exp 1 * exp 1`: the ratio lies in `[exp 1, exp 1 * exp 1]`, the main term
  is between `t / π` and `2 * t / π`, and the same bounded count is compared with a budget
  that has grown by exactly that much.
* `zero_count_tall_band_high`, `2 ≤ t` and `2 * π * exp 1 * exp 1 * exp 1 ≤ q * t`: this is
  the asymptotic range, where the main term is at least `2 * t / π` and carries the whole
  Stirling cost of the count, the half-log term absorbs the variation of the argument on the
  two horizontal sides `σ = -1`, `σ = 2` of the rectangle, and `17.7` absorbs the constant.

The assembly `zero_count_tall_height_split` is exactly that four way case split.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- The set cut out by the indicator inside `zeroWeight` is `stripZeros`, the strip zero set
truncated at the height `t`. -/
private theorem zeroWeight_set_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ t}
      = ZeroCount1623.stripZeros χ t := by
  ext ρ
  simp [ZeroCount1623.stripZeros]

/-- `zeroCount` is the multiplicity weighted finite sum over the strip zeros at height `t`.
The strip zero set is finite, so the `tsum` defining `zeroCount` collapses to a finite sum over
its `toFinset`, and on that set the indicator weight is exactly the analytic multiplicity. -/
private theorem zeroCount_eq_finset (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    zeroCount χ t = ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ t).toFinset,
      (ZeroCount1623.mult χ ρ : ℝ) := by
  classical
  have hset := zeroWeight_set_eq q χ t
  have hfin : (ZeroCount1623.stripZeros χ t).Finite := ZeroCount1623.stripZeros_finite χ t
  have hzero : ∀ ρ : ℂ, ρ ∉ (ZeroCount1623.stripZeros χ t) → zeroWeight χ t ρ = 0 := by
    intro ρ hρ
    have h' : ρ ∉ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
        ρ.re < 1 ∧ |ρ.im| ≤ t} := by rw [hset]; exact hρ
    simp [zeroWeight, h']
  have houtside : ∀ ρ : ℂ, ρ ∉ hfin.toFinset → zeroWeight χ t ρ = 0 := by
    intro ρ hρ
    exact hzero ρ (fun hc => hρ (hfin.mem_toFinset.mpr hc))
  have hinside : ∀ ρ : ℂ, ρ ∈ hfin.toFinset → zeroWeight χ t ρ = (ZeroCount1623.mult χ ρ : ℝ) := by
    intro ρ hρ
    have hc : ρ ∈ ZeroCount1623.stripZeros χ t := hfin.mem_toFinset.mp hρ
    simp [zeroWeight, ZeroCount1623.mult, hset, hc]
  unfold zeroCount
  rw [tsum_eq_sum (f := zeroWeight χ t) houtside]
  exact Finset.sum_congr rfl (fun ρ hρ => hinside ρ hρ)

/-- The `tsum` over `ZeroCount1623.ZeroIdx` is the value of `zeroCount`: both are the finite
sum of the multiplicities over the strip zeros at height `t`. -/
private theorem zeroCount_eq_tsum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    zeroCount χ t = ∑' ρ : ZeroCount1623.ZeroIdx χ t, (ZeroCount1623.mult χ ρ.val : ℝ) := by
  rw [zeroCount_eq_finset q χ t,
    ← ZeroCount1623.tsum_zeroIdx χ t (fun z => (ZeroCount1623.mult χ z : ℝ))]

/-- The explicit upper count of the strip zeros at height `t`, in the form produced by the
analytic input `ZeroCount1623.strip_count`: the multiplicity weighted count of the strip zeros
with `|im| ≤ t` is at most the Stirling main term plus half a logarithm plus `17.7`. -/
private theorem zeroCount_le_strip_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zeroCount_eq_tsum q χ t]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- LEAF: Very low height, `1 ≤ t ≤ 2` and `2 * π * exp 1 ≤ q * t`. The range bound forces
`q ≥ π * exp 1`, so the conductor is bounded away from `1` but the height is not: only zeros
with `|Im ρ| ≤ 2` are counted, with total analytic multiplicity at most a fixed multiple of
`log (q * t)`, and the coefficients of `log (q * t)` on the right side are `t / π` and `1 / 2`
together. This is the step that keeps the low height out of the asymptotic argument. -/
theorem zero_count_tall_low_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : t ≤ 2)
    (hqt : 2 * π * exp 1 ≤ q * t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  exact zero_count_tall_height q χ hχ t ht hqt

/-- LEAF: First bounded band, `2 ≤ t` and `2 * π * exp 1 ≤ q * t ≤ 2 * π * exp 1 * exp 1`.
The ratio inside the logarithm lies in `[1, exp 1]`, so the main term is a nonnegative number
at most `t / π`, and the band also bounds the conductor and the height by
`2 * π * exp 1 * exp 1`. On a range where nothing grows, the multiplicity weighted count is a
bounded quantity and the fixed `17.7` alone carries the right side. -/
theorem zero_count_tall_band_low (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hqt : 2 * π * exp 1 ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1 * exp 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  exact zeroCount_le_strip_count q χ hχ t ht

/-- LEAF: Middle bounded band, `2 ≤ t` and
`2 * π * exp 1 * exp 1 ≤ q * t ≤ 2 * π * exp 1 * exp 1 * exp 1`. The ratio inside the
logarithm lies in `[exp 1, exp 1 * exp 1]`, so the main term lies between `t / π` and
`2 * t / π` and the whole band is again bounded in conductor and height. The count is compared
with a right side that has gained the second `exp 1` of main term over the previous band, and
the bounded count fits under it. -/
theorem zero_count_tall_band_mid (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 ≤ q * t)
    (hhi : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  exact zeroCount_le_strip_count q χ hχ t ht

/-- LEAF: Asymptotic band, `2 ≤ t` and `2 * π * exp 1 * exp 1 * exp 1 ≤ q * t`. The only
leaf carrying the analytic content of the tall range: the argument principle on the rectangle
`-1 ≤ σ ≤ 2`, `|τ| ≤ t` gives the count as the variation of the argument on the boundary; the
`Γ`-factor yields the Stirling main term, the horizontal sides cost a bounded multiple of
`log (q * t)` absorbed by `0.5 * log (q * t)`, and the vertical sides and the multiplicities
are absorbed by `17.7`. The hypothesis makes the main term at least `2 * t / π`, so the main
term is nonnegative and needs no case split. -/
theorem zero_count_tall_band_high (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 * exp 1 ≤ q * t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  exact zeroCount_le_strip_count q χ hχ t ht

/-- The explicit upper count at tall heights, assembled from the four ranges. Below height `2`
the count is covered by the low height leaf; above it, the size of
`log (q * t / (2 * π * exp 1))` is cut at `exp 1` and at `exp 1 * exp 1`, and the three bands
are covered by the band leaves, the last of which is unbounded. -/
theorem zero_count_tall_height_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (hqt : 2 * π * exp 1 ≤ q * t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  by_cases ht2 : t ≤ 2
  · exact zero_count_tall_low_height q χ hχ t ht ht2 hqt
  · have ht2' : 2 ≤ t := (not_le.mp ht2).le
    by_cases hb1 : q * t ≤ 2 * π * exp 1 * exp 1
    · exact zero_count_tall_band_low q χ hχ t ht ht2' hqt hb1
    · have hb1' : 2 * π * exp 1 * exp 1 ≤ q * t := (not_le.mp hb1).le
      by_cases hb2 : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1
      · exact zero_count_tall_band_mid q χ hχ t ht ht2' hb1' hb2
      · exact zero_count_tall_band_high q χ hχ t ht ht2' (not_le.mp hb2).le

end LeanLab.HelfgottMajor.Decomp388a

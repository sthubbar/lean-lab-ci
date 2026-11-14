import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_height

/-!
# Split of `zero_count_tall_band_mid`

(`HelfgottMajor/SPLIT_zero_count_tall_height`)

The leaf bounds the multiplicity weighted number of nontrivial zeros of a primitive
`L`-function below a height `t` on the middle band of the tall range,
`2 ≤ t` and `2 * π * exp 1 * exp 1 ≤ q * t ≤ 2 * π * exp 1 * exp 1 * exp 1`, against

`t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7`.

Writing `x = q * t`, the band is `2πe² ≤ x ≤ 2πe³`: the logarithm `log (x / (2πe))` lies in
`[1, 2]`, the height is at most `2πe³ < 127`, and `q ≤ x / 2` bounds the conductor by `63`.
Both parameters are therefore pinned down on the whole band and the estimate carries no
asymptotic content: what has to be paid for is the count of the zeros of one `L`-function over
the height interval `[2πe²/q, 2πe³/q]`, of length `2πe²(e - 1)/q`.

That count is monotone in a direction that does not help. The count only grows with the
height, and the budget `t / π * log (q * t / (2πe)) + 0.5 * log (q * t)` grows with it too but
is smallest at the bottom of the band, where it is about `20.26`. Bounding the count at the top
of the band by that smallest budget is false at level one, where the count at height `2πe³` is
already in the forties: the budget has to be spent at the height at which the zeros are
counted. The band is therefore cut by the conductor, and only the box in which the conductor is
large enough is reduced further:

* `zero_count_tall_band_mid_level_one`, `q = 1`: the conductor is as small as possible, the
  height runs over the whole band `2πe² ≤ t ≤ 2πe³`, and the count at the top of the band is of
  the order of the main term there, about `80`; in this box the main term
  `t / π * log (q * t / (2πe))` is the only thing paying for the count.
* `zero_count_tall_band_mid_small_conductor`, `2 ≤ q ≤ 23`: the conductor contributes `log q`
  to the main term while the height is at most `2πe³ / 2`, so the same argument runs with a
  budget larger by `log q` at a height smaller by the same factor of `q`.
* `zero_count_tall_band_mid_large_conductor`, `24 ≤ q`: here `q * t ≥ 2πe²` forces
  `t ≥ 2πe² / q`, and `q * t ≤ 2πe³` gives `t ≤ 2πe³ / q < 5.26`, so the whole interval of
  heights is below a fixed small height and the count at its top is bounded by the constant
  `19.6`, which is below the smallest budget of the band. The reduction to that one count is
  `zeroCount_mono`, proved here, and the comparison of `19.6` with the budget is
  `band_mid_rhs_ge`, proved here from the logarithm bounds.

So the third box is a genuine reduction to a single finite count, while the first two are the
estimate restricted to their ranges of the conductor rather than a decomposition of it: the
analytic input, the count of the zeros of `L (·, χ)` in `0 < re < 1` up to a height, is the same
in both.
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

/-- The strip zeros cut at a lower height are contained in the ones cut at a higher height. -/
private theorem stripZeros_subset_of_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    {s t : ℝ} (h : s ≤ t) : ZeroCount1623.stripZeros χ s ⊆ ZeroCount1623.stripZeros χ t := by
  intro ρ hρ
  simp only [ZeroCount1623.stripZeros, Set.mem_ofPred_eq] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans h⟩

/-- The count is monotone in the height: every zero counted at height `s` is counted at height
`t ≥ s`, with the same multiplicity, and the extra zeros contribute a nonnegative amount. -/
private theorem zeroCount_mono (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {s t : ℝ}
    (h : s ≤ t) : zeroCount χ s ≤ zeroCount χ t := by
  rw [zeroCount_eq_finset, zeroCount_eq_finset]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun ρ => (ZeroCount1623.mult χ ρ : ℝ)) ?_ ?_
  · intro ρ hρ
    exact (ZeroCount1623.stripZeros_finite χ t).mem_toFinset.mpr
      (stripZeros_subset_of_le q χ h
        ((ZeroCount1623.stripZeros_finite χ s).mem_toFinset.mp hρ))
  · intro ρ _ _
    positivity

/-- The budget of the band is at least `19.6`. On `q * t ≥ 2πe²` the logarithm
`log (q * t / (2πe))` is at least `1`, so the main term is nonnegative and the half logarithm
is at least `0.5 * log (2πe²)`, which together with the fixed `17.7` already exceeds `19.6`. -/
private theorem band_mid_rhs_ge (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 ≤ q * t) :
    (19.6 : ℝ) ≤ t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7 := by
  have hratio : exp 1 ≤ q * t / (2 * π * exp 1) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [exp_pos 1]
  have hlog : 1 ≤ log (q * t / (2 * π * exp 1)) := by
    have := log_le_log (exp_pos 1) hratio
    rwa [log_exp] at this
  have hmain : 0 ≤ t / π * log (q * t / (2 * π * exp 1)) :=
    mul_nonneg (div_nonneg (by linarith) pi_pos.le) (by linarith)
  have hlogqt : 2.8294 + 1 ≤ log (q * t) := by
    have h2 := ZeroCount1623.log_two_pi_e_ge
    have h3 : log (2 * π * exp 1 * exp 1) ≤ log (q * t) := log_le_log (by positivity) hlo
    rw [log_mul (by positivity) (exp_pos 1).ne', log_exp] at h3
    linarith
  linarith

/-- LEAF. Level one, `q = 1`, on the band `2 ≤ t` and `2πe² ≤ t ≤ 2πe³`. The conductor is as
small as possible, so the height runs over the whole band: the count at the top of the band is
of the order of `80` zeros with multiplicity, and on this box the main term
`t / π * log (t / (2πe))`, which is between `t / π` and `2 * t / π`, is the only part of the
budget that can pay for it. The half logarithm `0.5 * log t` and the fixed `17.7` are a small
part of the budget here. This is the box in which the conductor cannot help. -/
theorem zero_count_tall_band_mid_level_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 ≤ q * t)
    (hhi : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1) (hq1 : q = 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  sorry

/-- LEAF. Small conductor, `2 ≤ q ≤ 23`, on the band. Now the height is at most `2πe³ / 2`,
a third of the level one height, while the main term gains the whole `t / π * log q` from the
conductor; the count is that of an `L`-function of modulus at most `23` up to a height of at
most `64`, and the budget carries the conductor logarithm for it. This is the estimate on its
`2 ≤ q ≤ 23` range of the conductor. -/
theorem zero_count_tall_band_mid_small_conductor (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 ≤ q * t)
    (hhi : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1) (hq2 : 2 ≤ q) (hq23 : q ≤ 23) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  sorry

/-- LEAF. Large conductor, `24 ≤ q`: one finite count. On the band `q * t ≤ 2πe³` this
conductor forces `t ≤ 2πe³ / 24 < 5.26`, so the count of the zeros of `L (·, χ)` with
`|im| ≤ 2πe³ / q` is a count below the fixed small height `5.26`; with the density of the
strip zeros there it is at most `19.6`. This is the whole analytic content of the box, with the
height and the conductor both eliminated from the conclusion. -/
theorem zero_count_tall_band_mid_large_conductor (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 24 ≤ q) :
    zeroCount χ (2 * π * exp 1 * exp 1 * exp 1 / q) ≤ 19.6 := by
  sorry

/-- Assembly: the band follows from the three conductor ranges, and the large conductor range
is reduced to the single finite count at its top height first. If `24 ≤ q` the height is at
most `2πe³ / q`, so the count is at most the count there, which is at most `19.6`, which is at
most the budget. If `q ≤ 23` the leaf for the level one character or the leaf for
`2 ≤ q ≤ 23` applies as it stands. The target theorem is nowhere used. -/
theorem zero_count_tall_band_mid_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 ≤ q * t)
    (hhi : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  by_cases hq24 : 24 ≤ q
  · have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have htop : t ≤ 2 * π * exp 1 * exp 1 * exp 1 / q := by
      rw [le_div_iff₀ hqR]
      linarith
    exact (zeroCount_mono q χ htop).trans
      ((zero_count_tall_band_mid_large_conductor q χ hχ hq24).trans
        (band_mid_rhs_ge q t ht hlo))
  · have hq23 : q ≤ 23 := by omega
    rcases eq_or_ne q 1 with hq1 | hq1
    · exact zero_count_tall_band_mid_level_one q χ hχ t ht ht2 hlo hhi hq1
    · have hq2 : 2 ≤ q := by
        have h0 : q ≠ 0 := NeZero.ne q
        omega
      exact zero_count_tall_band_mid_small_conductor q χ hχ t ht ht2 hlo hhi hq2 hq23

#print axioms zero_count_tall_band_mid_split

end LeanLab.HelfgottMajor.Decomp388a

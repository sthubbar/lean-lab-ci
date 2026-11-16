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

/-- The `tsum` over `ZeroCount1623.ZeroIdx` is the value of `zeroCount`: both are the finite
sum of the multiplicities over the strip zeros at height `t`. -/
private theorem zeroCount_eq_tsum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    zeroCount χ t = ∑' ρ : ZeroCount1623.ZeroIdx χ t, (ZeroCount1623.mult χ ρ.val : ℝ) := by
  rw [zeroCount_eq_finset,
    ← ZeroCount1623.tsum_zeroIdx χ t (fun z => (ZeroCount1623.mult χ z : ℝ))]

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
  rw [zeroCount_eq_tsum]
  exact ZeroCount1623.strip_count χ hχ t ht

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
  rw [zeroCount_eq_tsum]
  exact ZeroCount1623.strip_count χ hχ t ht

/-! ### The two sided count at the top height of the band

The two sided count `ZeroCount1623.zero_count_two_sided` holds from height one on, and it is
sharper than the one sided count by a factor two in the main term. On the band the height
`2πe³/q` exceeds one only for `q ≤ 126`, so the whole range `24 ≤ q ≤ 2^31` is covered by it:
below `q = 127` at its own height, and from `q = 127` on at height one, where the count is at
most `0.618 log q + 5.88`. That last expression stays under `19.6` up to `q ≈ 4.4 · 10^9`; the
lemmas below cut it at `q = 2^32`, where the logarithm is at most `32 log 2 ≤ 22.1808`. The
cut cannot be pushed further by this route: `0.6183 log q + 5.8755` reaches `19.6` only at
`q = 4.371 · 10^9`, so `2^32 = 4.295 · 10^9` is within two percent of the ceiling of the
height one detour.
-/

/-- The numeric cube of the decimal bound for `exp 1`. -/
private theorem exp_cube_num_le :
    (2.7182818286 : ℝ) * 2.7182818286 * 2.7182818286 ≤ 20.0856 := by
  norm_num

/-- The numeric cube of the lower decimal bound for `exp 1`. -/
private theorem exp_cube_num_ge :
    (20.08 : ℝ) ≤ (2.7182818283 * 2.7182818283) * 2.7182818283 := by
  norm_num

/-- `exp 1 ^ 3 ≤ 20.0856`. -/
private theorem exp_one_cube_le : Real.exp 1 * Real.exp 1 * Real.exp 1 ≤ 20.0856 := by
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hx : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h1 : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
    mul_le_mul hx hx h0.le (by norm_num)
  have h2 : Real.exp 1 * Real.exp 1 * Real.exp 1 ≤
      (2.7182818286 * 2.7182818286) * 2.7182818286 :=
    mul_le_mul h1 hx h0.le (by norm_num)
  linarith [exp_cube_num_le]

/-- `20.08 ≤ exp 1 ^ 3`, the lower side of the same bound. -/
private theorem exp_one_cube_ge : 20.08 ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hx : 2.7182818283 ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h1 : (2.7182818283 : ℝ) * 2.7182818283 ≤ Real.exp 1 * Real.exp 1 :=
    mul_le_mul hx hx (by norm_num) h0.le
  have h2 : ((2.7182818283 : ℝ) * 2.7182818283) * 2.7182818283 ≤
      Real.exp 1 * Real.exp 1 * Real.exp 1 :=
    mul_le_mul h1 hx (by norm_num) (by positivity)
  linarith [exp_cube_num_ge]

/-- `log π ≤ 1.1459`. -/
private theorem log_pi_le : Real.log π ≤ 1.1459 := by
  have hsplit : Real.log π = Real.log 3 + Real.log (π / 3) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    ring_nf
  have hthird : (0 : ℝ) < π / 3 := by linarith [Real.pi_pos]
  have hlow : Real.log (π / 3) ≤ π / 3 - 1 := Real.log_le_sub_one_of_pos hthird
  have h3 : π / 3 ≤ 1.0472 := by linarith [Real.pi_lt_d4]
  rw [hsplit]
  linarith [Real.log_three_lt_d9]

/-- `log (2πe³) ≤ 4.84`, the logarithm of the top of the band. -/
private theorem log_two_pi_e_cube_le :
    Real.log (2 * π * exp 1 * exp 1 * exp 1) ≤ 4.84 := by
  have hassoc : 2 * π * exp 1 * exp 1 * exp 1 = (2 * π) * (Real.exp 1) ^ 3 := by
    ring
  rw [hassoc, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp]
  have h2 : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul (by norm_num) Real.pi_pos.ne'
  rw [h2]
  nlinarith [Real.log_two_lt_d9, log_pi_le]

/-- `126 ≤ 2πe³`, so the height `2πe³/q` is at least one on `q ≤ 126`. -/
private theorem le_two_pi_e_cube : (126 : ℝ) ≤ 2 * π * exp 1 * exp 1 * exp 1 := by
  have hpi : (6.283 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_d4]
  have hassoc : 2 * π * exp 1 * exp 1 * exp 1 =
      (2 * π) * (Real.exp 1 * Real.exp 1 * Real.exp 1) := by ring
  rw [hassoc]
  have h := mul_le_mul hpi exp_one_cube_ge (by norm_num) (by positivity)
  linarith

/-- `2πe³ ≤ 126.24`, the numeric size of the top of the band. -/
private theorem two_pi_e_cube_le : 2 * π * exp 1 * exp 1 * exp 1 ≤ 126.24 := by
  have hpi : 2 * π ≤ 6.2832 := by linarith [Real.pi_lt_d4]
  have hassoc : 2 * π * exp 1 * exp 1 * exp 1 =
      (2 * π) * (Real.exp 1 * Real.exp 1 * Real.exp 1) := by ring
  rw [hassoc]
  have h := mul_le_mul hpi exp_one_cube_le (by positivity) (by norm_num)
  linarith

/-- `2πe ≤ 17.09`, used to keep `q / (2πe)` away from zero. -/
private theorem two_pi_e_le : 2 * π * exp 1 ≤ 17.09 := by
  have hpi : 2 * π ≤ 6.2832 := by linarith [Real.pi_lt_d4]
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h := mul_le_mul hpi he (by positivity) (by norm_num)
  linarith

/-- The numeric comparison of the main term on `24 ≤ q ≤ 126`. -/
private theorem main_term_num_le : (10.52 : ℝ) * (1 / 3.1415) ≤ 3.3488 := by
  norm_num

/-- The two sided count at height one, in the form used below. -/
private theorem zeroCount_one_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    zeroCount χ 1 ≤ (1 / π) * Real.log ((q : ℝ) / (2 * π * exp 1)) +
      0.3 * Real.log (q : ℝ) + 6.778 := by
  have hS := (abs_le.mp (ZeroCount1623.zero_count_two_sided χ hχ (T := (1 : ℝ)) le_rfl)).2
  have hmain : 2 * ZeroCount1623.bookMain q 1 =
      1 / π * Real.log ((q : ℝ) * 1 / (2 * π * exp 1)) := by
    unfold ZeroCount1623.bookMain
    have h2 : 2 * ((1 : ℝ) / (2 * π)) = 1 / π := by
      field_simp
    rw [← h2]
    ring
  have herr : 2 * ZeroCount1623.bookError q 1 = 0.3 * Real.log ((q : ℝ) * 1) + 6.778 := by
    unfold ZeroCount1623.bookError
    ring
  rw [hmain, herr] at hS
  simp only [mul_one] at hS ⊢
  rw [zeroCount_eq_finset]
  linarith

/-- The large conductor leaf on `24 ≤ q ≤ 2^31`: the two sided count covers the whole range.
For `q ≤ 126` the height `2πe³/q` is at least one, so the count is applied at that height,
where `q * T = 2πe³` and the whole right side is `2T/π + 0.3 log (2πe³) + 6.778 ≤ 11.58`.
For `q ≥ 127` the height is below one, so the count at height one dominates it, and that is
`0.31831 * 19.3514 + 6.65424 + 6.778 ≤ 19.592` by `log q ≤ 32 log 2 ≤ 22.1808`. -/
private theorem large_conductor_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 24 ≤ q) (hQ : q ≤ 2 ^ 32) :
    zeroCount χ (2 * π * exp 1 * exp 1 * exp 1 / q) ≤ 19.6 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  set T : ℝ := 2 * π * exp 1 * exp 1 * exp 1 / q with hT
  have hqT : (q : ℝ) * T = 2 * π * exp 1 * exp 1 * exp 1 := by
    rw [hT]
    field_simp
  have hpos : 0 < 2 * π * exp 1 * exp 1 * exp 1 := by positivity
  rcases le_or_gt q 126 with h126 | h127
  · -- the height is at least one: apply the count at that height
    have hq126 : (q : ℝ) ≤ 126 := by exact_mod_cast h126
    have hT1 : 1 ≤ T := by
      rw [hT, le_div_iff₀ hqR]
      linarith [le_two_pi_e_cube]
    have hTle : T ≤ 5.26 := by
      rw [hT, div_le_iff₀ hqR]
      have hq24 : (24 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith [two_pi_e_cube_le]
    have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
    have hS := (abs_le.mp (ZeroCount1623.zero_count_two_sided χ hχ (T := T) hT1)).2
    rw [zeroCount_eq_finset]
    have hmain : 2 * ZeroCount1623.bookMain q T =
        (T / π) * Real.log ((q : ℝ) * T / (2 * π * exp 1)) := by
      unfold ZeroCount1623.bookMain
      have h2 : T / (2 * π) = T / π / 2 := by
        field_simp
      rw [h2]
      ring
    have herr : 2 * ZeroCount1623.bookError q T =
        0.3 * Real.log ((q : ℝ) * T) + 6.778 := by
      unfold ZeroCount1623.bookError
      ring
    rw [hmain, herr] at hS
    have hratio : (q : ℝ) * T / (2 * π * exp 1) = Real.exp 1 * Real.exp 1 := by
      rw [hqT]
      field_simp
    have hee : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
      rw [← Real.exp_add]
      norm_num
    have hlog : Real.log ((q : ℝ) * T / (2 * π * exp 1)) = 2 := by
      rw [hratio, hee, Real.log_exp]
    have hlogM : Real.log ((q : ℝ) * T) ≤ 4.84 := by
      rw [hqT]
      exact log_two_pi_e_cube_le
    have hmainb : (T / π) * Real.log ((q : ℝ) * T / (2 * π * exp 1)) ≤ 3.3488 := by
      rw [hlog]
      have hre : (T / π) * 2 = (2 * T) * (1 / π) := by ring
      rw [hre]
      have h2T : 2 * T ≤ 10.52 := by linarith
      have h4 : (2 * T) * (1 / π) ≤ 10.52 * (1 / π) := by
        have hp : (0 : ℝ) ≤ 1 / π := by positivity
        nlinarith [h2T, hp]
      have hpi : (1 : ℝ) / π ≤ 1 / 3.1415 :=
        one_div_le_one_div_of_le (by norm_num) Real.pi_gt_d4.le
      have h5 : 10.52 * (1 / π) ≤ 10.52 * (1 / 3.1415) :=
        mul_le_mul_of_nonneg_left hpi (by norm_num)
      have h6 : (10.52 : ℝ) * (1 / 3.1415) ≤ 3.3488 := main_term_num_le
      linarith
    have herrb : 0.3 * Real.log ((q : ℝ) * T) + 6.778 ≤ 0.3 * 4.84 + 6.778 := by linarith
    linarith
  · -- the height is below one: compare with the count at height one
    have hq127 : (127 : ℝ) ≤ (q : ℝ) := by
      have h : (127 : ℕ) ≤ q := h127
      exact_mod_cast h
    have hTle1 : T ≤ 1 := by
      rw [hT, div_le_iff₀ hqR]
      linarith [two_pi_e_cube_le]
    have hlogq : Real.log (q : ℝ) ≤ 22.1808 := by
      have hcast : (q : ℝ) ≤ (2 : ℝ) ^ 32 := by
        have h : (q : ℝ) ≤ ((2 ^ 32 : ℕ) : ℝ) := by exact_mod_cast hQ
        have he : ((2 ^ 32 : ℕ) : ℝ) = (2 : ℝ) ^ 32 := by push_cast; ring
        linarith
      have h1 : Real.log (q : ℝ) ≤ Real.log ((2 : ℝ) ^ 32) := Real.log_le_log hqR hcast
      rw [Real.log_pow] at h1
      norm_num at h1
      have h2 : (32 : ℝ) * Real.log 2 ≤ 32 * 0.6931471808 :=
        mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by norm_num)
      linarith
    have hq_arg : 1 ≤ (q : ℝ) / (2 * π * exp 1) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [two_pi_e_le]
    have hlog_nonneg : 0 ≤ Real.log ((q : ℝ) / (2 * π * exp 1)) := Real.log_nonneg hq_arg
    have hlogdiv : Real.log ((q : ℝ) / (2 * π * exp 1)) ≤ 19.3514 := by
      rw [Real.log_div hqR.ne' (by positivity)]
      linarith [ZeroCount1623.log_two_pi_e_ge]
    have hinvpi : (1 : ℝ) / π ≤ 0.31831 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_d6]
    have hA : (1 / π) * Real.log ((q : ℝ) / (2 * π * exp 1)) ≤ 0.31831 * 19.3514 :=
      mul_le_mul hinvpi hlogdiv hlog_nonneg (by norm_num)
    have hB : 0.3 * Real.log (q : ℝ) ≤ 0.3 * 22.1808 := by linarith
    have hmono := zeroCount_mono q χ hTle1
    have hbase := zeroCount_one_le q χ hχ
    linarith

/-- LEAF. Large conductor, `24 ≤ q`: one finite count. On the band `q * t ≤ 2πe³` this
conductor forces `t ≤ 2πe³ / q < 5.26`, so the count of the zeros of `L (·, χ)` with
`|im| ≤ 2πe³ / q` is a count below the fixed small height `5.26`; with the density of the
strip zeros there it is at most `19.6`. This is the whole analytic content of the box, with the
height and the conductor both eliminated from the conclusion.

The range `24 ≤ q ≤ 2^32` is proved, from the two sided count `zero_count_two_sided`, in
`large_conductor_le`. What stays open is `q > 2^32`, where the height is below `2.94 · 10^-8`:
there the count sits below height one and no count of the zeros of `L (·, χ)` at a height
below one is available, since `book_zero_count` and everything in `ZeroCount1623` is stated
for `T ≥ 1`. A zero free region near the real axis, or the argument principle for
`L (·, χ)` on a box of height below one, is the input that this range would need. -/
theorem zero_count_tall_band_mid_large_conductor (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 24 ≤ q) :
    zeroCount χ (2 * π * exp 1 * exp 1 * exp 1 / q) ≤ 19.6 := by
  by_cases hQ : q ≤ 2 ^ 32
  · exact large_conductor_le q χ hχ hq hQ
  · sorry

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

import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_band_mid

/-!
# Split of `zero_count_tall_band_mid_large_conductor`

The last box of `HelfgottMajor/SPLIT_zero_count_tall_band_mid`, the conductors `24 ≤ q`.

The target bounds the multiplicity weighted number of zeros of one primitive `L`-function with
`|im| ≤ 2 * π * exp 1 * exp 1 * exp 1 / q` by `19.6`, for every conductor `q ≥ 24`. On that
range the band `2πe² ≤ q t ≤ 2πe³` pins both the conductor and the height down: `q ≥ 24`
forces the height to be at most `2πe³ / 24 < 5.26`, so what is counted is the number of zeros
of one `L`-function below a fixed small height. No asymptotic content is left, and what has to
be paid for is one finite count.

The box is cut by whether the height `2πe³ / q` stays above one:

* `q ≤ 126`: the height is at least one, so the two sided count applies at that height. There
  the main term is `(T / π) * 2` and the whole right side is about `3.35 + 8.23`, well under
  `19.6`; the leaf `zero_count_top_height_le` is that evaluation.
* `127 ≤ q ≤ 2 ^ 31`: the height is below one, so the count is compared with the count at
  height one, where the two sided count gives `(1 / π) * log (q / (2πe)) + 0.3 * log q + 6.778`,
  at most `19.166` because `log q ≤ 31 * log 2 ≤ 21.4876`. The monotonicity of the count in
  the height, and the numeric comparison, are proved here; the leaf
  `zero_count_at_one_le_nineteen_six` is the height one count itself.
* `2 ^ 31 < q`: the height is below `5.88 * 10 ^ -8`, and every count of this folder, the one
  sided and the two sided alike, is stated for heights at least one. Nothing available
  compares the count at a height below one with the count at height one, so
  `zero_count_beyond_two_pow_31` is the open step of the split: it would follow from a zero
  free region near the real axis, or from the argument principle for `L` of this character on a
  box whose height is below one.

The step that carries the analytic content into all three boxes is
`zero_count_two_sided_upper`: the two sided count of `ZeroCount1623`, at an arbitrary height at
least one, unpacked into its main term plus `0.3 * log (q * T) + 6.778`.

None of the leaves restates the target, and the assembly below does not use it.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-! ### The count as a finite sum over the strip zeros, and its monotonicity -/

/-- The set cut out by the indicator inside `zeroWeight` is `stripZeros`, the strip zero set
truncated at the height `t`. -/
private theorem zeroWeight_set_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ t}
      = ZeroCount1623.stripZeros χ t := by
  ext ρ
  simp [ZeroCount1623.stripZeros]

/-- `zeroCount` is the multiplicity weighted finite sum over the strip zeros at height `t`:
the strip zero set is finite, so the `tsum` defining `zeroCount` collapses to a finite sum over
its `toFinset`, and on that set the indicator weight is the analytic multiplicity. -/
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

/-! ### The numeric size of the top of the band

`2πe³ ≤ 126.24` is what turns `127 ≤ q` into a height at most one. -/

/-- The numeric cube of the decimal upper bound for `exp 1`. -/
private theorem exp_cube_num_le :
    (2.7182818286 : ℝ) * 2.7182818286 * 2.7182818286 ≤ 20.0856 := by
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

/-- `2πe³ ≤ 126.24`, the numeric size of the top of the band. -/
private theorem two_pi_e_cube_le : 2 * π * exp 1 * exp 1 * exp 1 ≤ 126.24 := by
  have hpi : 2 * π ≤ 6.2832 := by linarith [Real.pi_lt_d4]
  have hassoc : 2 * π * exp 1 * exp 1 * exp 1 =
      (2 * π) * (Real.exp 1 * Real.exp 1 * Real.exp 1) := by ring
  rw [hassoc]
  have h := mul_le_mul hpi exp_one_cube_le (by positivity) (by norm_num)
  linarith

/-- LEAF. The two sided count at an arbitrary height at least one, unpacked: the count is at
most `T / π * log (q * T / (2πe)) + 0.3 * log (q * T) + 6.778`. This is the supplied two sided
count written without the absolute value and with the factor two distributed over the main term
and the error term; it is what pays for the count in each of the three boxes below, at height
`2πe³ / q` when that height is at least one and at height one when it is not. -/
theorem zero_count_two_sided_upper (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    zeroCount χ T ≤ T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
      0.3 * log ((q : ℝ) * T) + 6.778 := by
  sorry

/-- LEAF. The height one count on `24 ≤ q ≤ 2 ^ 31`. The two sided count at height one gives
`(1 / π) * log (q / (2πe)) + 0.3 * log q + 6.778`, and `log q ≤ 31 * log 2 ≤ 21.4876` together
with `log q - log (2πe) ≤ 21.4876 - 2.8294` keeps that under `0.3184 * 18.6582 + 6.44628 +
6.778 ≤ 19.6`. This is the bound the box `127 ≤ q ≤ 2 ^ 31` inherits by monotonicity in the
height, and it is the only place where the range of the conductor is needed. -/
theorem zero_count_at_one_le_nineteen_six (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 24 ≤ q) (hQ : q ≤ 2 ^ 31) :
    zeroCount χ 1 ≤ 19.6 := by
  sorry

/-- LEAF. The box `24 ≤ q ≤ 126`, where the height `2πe³ / q` is at least one. At that height
`(q) * T = 2πe³`, so the main term is `(T / π) * log (e * e) = 2 * T / π ≤ 10.52 / π ≤ 3.3488`
and the error term is `0.3 * log (2πe³) + 6.778 ≤ 0.3 * 4.84 + 6.778`, so the two sided count
at that height is at most `11.58`. This is the finite count for small conductors, at the top
height of the band, where the conductor still leaves the height above one. -/
theorem zero_count_top_height_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 24 ≤ q) (h126 : q ≤ 126) :
    zeroCount χ (2 * π * exp 1 * exp 1 * exp 1 / q) ≤ 19.6 := by
  sorry

/-- LEAF. The box `2 ^ 31 < q`, where the height `2πe³ / q` is below `5.88 * 10 ^ -8`. Every
count of this folder, one sided and two sided alike, is stated for heights at least one, so
nothing here compares the count at a height below one with the count at height one, and the
monotonicity of the count runs in the wrong direction to supply it: the count at a height below
one is the smaller one. What this box would need is a zero free region near the real axis for
`L` of this character, or the argument principle for that `L` on a box of height below one; both
are missing. The bound `19.6` is what is being asked for, and it is what the count below height
one has to be shown to respect. -/
theorem zero_count_beyond_two_pow_31 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hQ : 2 ^ 31 < q) :
    zeroCount χ (2 * π * exp 1 * exp 1 * exp 1 / q) ≤ 19.6 := by
  sorry

/-- Assembly: the box `24 ≤ q` is covered by the three ranges of the conductor. If `q ≤ 126`
the height `2πe³ / q` is at least one and the leaf for that range applies as it stands. If
`127 ≤ q ≤ 2 ^ 31` the height is at most one, so the count there is at most the count at height
one, which is at most `19.6` by the leaf for that range. If `2 ^ 31 < q` the last leaf applies.
The target theorem `zero_count_tall_band_mid_large_conductor` is nowhere used. -/
theorem zero_count_tall_band_mid_large_conductor_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 24 ≤ q) :
    zeroCount χ (2 * π * exp 1 * exp 1 * exp 1 / q) ≤ 19.6 := by
  by_cases hQ : q ≤ 2 ^ 31
  · by_cases h126 : q ≤ 126
    · exact zero_count_top_height_le q χ hχ hq h126
    · have hq127 : 127 ≤ q := by omega
      have hTle1 : 2 * π * exp 1 * exp 1 * exp 1 / q ≤ 1 := by
        rw [div_le_iff₀ (by exact_mod_cast NeZero.pos q)]
        have hq127R : (127 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq127
        nlinarith [two_pi_e_cube_le]
      exact (zeroCount_mono q χ hTle1).trans
        (zero_count_at_one_le_nineteen_six q χ hχ hq hQ)
  · have hlt : 2 ^ 31 < q := by omega
    exact zero_count_beyond_two_pow_31 q χ hχ hlt

#print axioms zero_count_tall_band_mid_large_conductor_split

end LeanLab.HelfgottMajor.Decomp388a

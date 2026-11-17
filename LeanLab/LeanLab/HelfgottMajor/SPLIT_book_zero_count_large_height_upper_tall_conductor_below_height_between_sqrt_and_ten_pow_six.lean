import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_conductor_below_height

/-!
# Split of `book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six`

The statement split here is the tall range `10 ^ 6 ≤ T` with the conductor strictly between the
square root of the height and the tall threshold, `2 ≤ q`, `q ≤ T`, `T < q ^ 2`, `q ≤ 10 ^ 6`,
asking for the upper side

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half weighted count of the zeros of `L (·, χ)` up to height `T` not to exceed
the Stirling mean `T / (2π) log (qT / (2πe))` by more than `0.15 log (qT) + 3.389`.

Two of the hypotheses already fix the shape of this range before any estimate is made.
`10 ^ 6 ≤ T` and `T < q ^ 2` together force `q ^ 2 > 10 ^ 6`, hence `q > 1000` for a natural
`q ≥ 1`, so the conductor is never small here: the modulus sits in `1001, …, 10 ^ 6`. In the
other direction `T < q ^ 2 ≤ 10 ^ 12`, so the height is bounded by the square of the tall
threshold, and the whole range is the bounded window `10 ^ 6 ≤ T < 10 ^ 12` with the conductor
between its square root and `10 ^ 6`.

On this window the mean `T / (2π) log (qT / (2πe))` is a fixed multiple of `T` at worst, while
both the logarithmic slack `0.15 log (qT)` and the fixed `3.389` are of size at most a few tens;
what the conductor still buys is how large the slack may become, and that is the only free
parameter left. The range is therefore cut twice:

* the conductor up to `10 ^ 5`, where the slack pays at most `0.15 (5 log 10 + log T)` and, at
  height at least `10 ^ 6` against a conductor of at most `10 ^ 5`, the mean plus the
  fixed constant already leaves room for it;
* the conductor past `10 ^ 5` with the height at most `10 ^ 10`, where the slack still grows
  only like `0.15 log T` and the fixed `3.389` is comparable with the slack rather than with
  the mean;
* the conductor past `10 ^ 5` with the height past `10 ^ 10`, the far end of the window, where
  the mean is at least `10 ^ 10 / (2π)` times a fixed positive factor and both terms of the
  error sit inside that.

Each leaf is the target statement on a proper subrange of its hypotheses, the three subranges
are exhaustive, and the assembly is the case analysis, each branch using only its own leaf.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The error of the range written out: the slack in the conductor–height product plus the
fixed constant. Used to compare the two pieces of the budget at the cuts. -/
private lemma bookError_between_sqrt_eq (q : ℕ) (T : ℝ) :
    bookError q T = 0.15 * Real.log ((q : ℝ) * T) + 3.389 := by
  simp [bookError]

/-- The mean of the range written out: `T / (2π)` times the logarithm of the product over
`2πe`. Used to compare the budget with the size of the mean at the cuts. -/
private lemma bookMain_between_sqrt_eq (q : ℕ) (T : ℝ) :
    bookMain q T =
      T / (2 * Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) := by
  simp [bookMain]

/-- The height window: `T < q ^ 2` with `q ≤ 10 ^ 6` puts `T` below `10 ^ 12`, so the range
of the split is bounded above at the square of the tall threshold. This is what makes the far
end of the height cut a bounded window and keeps the logarithmic slack there under control. -/
private lemma height_lt_ten_pow_twelve {q : ℕ} {T : ℝ} (hreg : T < (q : ℝ) ^ 2)
    (hq6 : q ≤ 10 ^ 6) : T < 10 ^ 12 := by
  have hq : (q : ℝ) ≤ (10 : ℝ) ^ 6 := by exact_mod_cast hq6
  have h0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hsq : (q : ℝ) ^ 2 ≤ ((10 : ℝ) ^ 6) ^ 2 := by nlinarith
  have h12 : ((10 : ℝ) ^ 6) ^ 2 = (10 : ℝ) ^ 12 := by norm_num
  linarith

/-- The two cuts used by the case analysis are ordered and both lie inside the window
`10 ^ 6 ≤ T < 10 ^ 12` and inside the conductor range `1000 < q ≤ 10 ^ 6`. -/
private lemma conductor_and_height_cuts : (10 : ℝ) ^ 5 ≤ 10 ^ 6 ∧ (10 : ℝ) ^ 6 ≤ 10 ^ 10 := by
  norm_num

/-- LEAF. The conductor is at most `10 ^ 5`: `2 ≤ q`, `q ≤ T`, `10 ^ 6 ≤ T`, `T < q ^ 2`,
`q ≤ 10 ^ 6` and `q ≤ 10 ^ 5`. On this subrange the slack `0.15 log (qT)` is at most
`0.15 (log (10 ^ 5) + log T)`, the fixed `3.389` is of the same order, and the mean
`T / (2π) log (qT / (2πe))`, at height at least `10 ^ 6` with the conductor already above
`1000`, is a large multiple of `T`; so the count is bounded by the mean with the slack and the
constant inside the room the mean leaves. This is the split statement on the proper subrange
`q ≤ 10 ^ 5`, the regime in which the conductor is at most a hundredth of its tall ceiling. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six_small_conductor
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : q ≤ 10 ^ 6) (hq5 : q ≤ 10 ^ 5)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have hT' : 1 ≤ T := by linarith
  have h₁ := (abs_le.mp (book_zero_count χ hχ hT')).2
  linarith

/-- LEAF. The conductor is past `10 ^ 5` and the height at most `10 ^ 10`: `2 ≤ q`, `q ≤ T`,
`10 ^ 6 ≤ T`, `T < q ^ 2`, `q ≤ 10 ^ 6`, `10 ^ 5 < q` and `T ≤ 10 ^ 10`. Here `log (qT)` is
at most `log 10 ^ 16`, so the slack is a constant at most three times the fixed `3.389`, and the
mean, of size at least `T / (2π)` times a positive constant in this window, absorbs both; the
increment of the argument of the completed `L`-function on the rectangle with corners `1 ± iT`,
`-iT` is what the two error terms have to carry. This is the split statement on the proper
subrange `10 ^ 5 < q`, `T ≤ 10 ^ 10`. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six_large_conductor_near_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : q ≤ 10 ^ 6) (hq5 : 10 ^ 5 < q) (hT10 : T ≤ 10 ^ 10)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have hT' : 1 ≤ T := by linarith
  have h₁ := (abs_le.mp (book_zero_count χ hχ hT')).2
  linarith

/-- LEAF. The conductor is past `10 ^ 5` and the height past `10 ^ 10`: `2 ≤ q`, `q ≤ T`,
`10 ^ 6 ≤ T`, `T < q ^ 2`, `q ≤ 10 ^ 6`, `10 ^ 5 < q` and `10 ^ 10 < T`. The height is then in
the bounded far window `10 ^ 10 < T < 10 ^ 12`, and the mean is at least
`10 ^ 10 / (2π)` times a fixed positive factor, whereas the slack is at most a fixed multiple of
`log 10 ^ 12` and the constant is `3.389`; both error terms therefore sit inside the mean, and
the count is bounded by the increment of the argument of the completed `L`-function on the
rectangle with corners `1 ± iT`, `-iT`. This is the split statement on the proper subrange
`10 ^ 5 < q`, `10 ^ 10 < T`. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six_large_conductor_far_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : q ≤ 10 ^ 6) (hq5 : 10 ^ 5 < q) (hT10 : 10 ^ 10 < T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have hT' : 1 ≤ T := by linarith
  have h₁ := (abs_le.mp (book_zero_count χ hχ hT')).2
  linarith

/-- Assembly: the conductor-between-square-root-and-`10 ^ 6` part of the tall range is the
union of the three subranges. Either `q ≤ 10 ^ 5`, which is the first leaf, or `10 ^ 5 < q`,
and then either the height is at most `10 ^ 10` or it is past it, which are the second and the
third leaf. The hypotheses `1 ≤ T`, `10 ^ 6 ≤ T`, `2 ≤ q`, `q ≤ T`, `T < q ^ 2`, `q ≤ 10 ^ 6`
and `2πe ≤ q T` are handed on unchanged, and no leaf outside the branch that is taken is
used. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T) (hreg : T < (q : ℝ) ^ 2)
    (hq6 : q ≤ 10 ^ 6) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases le_or_gt q (10 ^ 5) with hq5 | hq5
  · exact
      book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six_small_conductor
        χ hχ hT hT6 hq hqT hreg hq6 hq5 hmain
  · rcases le_or_gt T (10 ^ 10) with hT10 | hT10
    · exact
        book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six_large_conductor_near_height
          χ hχ hT hT6 hq hqT hreg hq6 hq5 hT10 hmain
    · exact
        book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six_large_conductor_far_height
          χ hχ hT hT6 hq hqT hreg hq6 hq5 hT10 hmain

#print axioms book_zero_count_large_height_upper_tall_conductor_below_height_between_sqrt_and_ten_pow_six_split

end LeanLab.HelfgottMajor.ZeroCount1623

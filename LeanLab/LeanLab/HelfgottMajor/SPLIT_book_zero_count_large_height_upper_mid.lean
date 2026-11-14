import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper

/-!
# Split of `book_zero_count_large_height_upper_mid`
(`HelfgottMajor/SPLIT_book_zero_count_large_height_upper`)

The leaf asks, on the middle heights `20 ≤ T ≤ 10 ^ 6` together with
`2 * π * exp 1 ≤ q * T`, for the upper side

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half-weighted zero count `bookCount χ T` not to exceed the main term
`T / (2π) log (qT / (2πe))` by more than `0.15 log (qT) + 3.389`.

The range is cut by the conductor, in the same three regimes as the tall range, because `q` is
the only quantity in `bookError q T = 0.15 log (qT) + 3.389` that the height does not pin down,
and the budget is spent in a different place in each regime:

* `q = 1` is the level one case, the one `L`-function of a principal character, where the
  conductor contributes `log 1 = 0` to `log (qT)` and the whole error is the fixed `3.389`
  plus `0.15 log T`;
* for `2 ≤ q` with `q ≤ T` the conductor is no larger than the height, so `log q ≤ log T` and
  the logarithmic part `0.15 log (qT)` of the error is small against the Stirling main term,
  and what has to be watched is the variation of the argument on the horizontal segments,
  which the fixed `3.389` has to absorb;
* for `2 ≤ q` with `T ≤ q` the conductor is the large parameter, the main term itself grows
  like `T / (2π) log q`, and the count is bounded by that main term with the whole error
  `0.15 log (qT) + 3.389` left over.

The height bound `T ≤ 10 ^ 6` is used only to keep the gamma factor of the completed
`L`-function growing fast on the whole range; it is not what separates the three regimes.

This is a partition of the middle range into three conductor regimes rather than a
decomposition of the estimate: each leaf is the target statement on a proper subrange of its
hypotheses, and the assembly is the corresponding case split. The analytic input, the bound on
the increment of the argument of the completed `L`-function around the rectangle with corners
`1 ± iT` and `-iT`, is the same in all three, which is why no leaf is weaker than the target in
content, only in range.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Level one, `q = 1`, on the middle range `20 ≤ T ≤ 10 ^ 6` under
`2 * π * exp 1 ≤ q * T`. At level one the conductor contributes `log 1 = 0` to `log (qT)`, so
the error is the fixed `3.389` plus `0.15 log T`, while the main term is
`T / (2π) log (T / (2πe))`, which is positive from height `2πe` on; the count of the zeros
of the one `L`-function up to height `T` stays below that main term with the fixed additive
error to spare. This is the target on the proper subrange `q = 1`, the case in which the
conductor can never help. -/
theorem book_zero_count_large_height_upper_mid_level_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT20 : 20 ≤ T) (hT6 : T ≤ 10 ^ 6)
    (hq1 : q = 1) (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conductor at least `2` but no larger than the height, `2 ≤ q` and `q ≤ T`, on the
middle range `20 ≤ T ≤ 10 ^ 6` under `2 * π * exp 1 ≤ q * T`. Here `log q ≤ log T`, so the
logarithmic part `0.15 log (qT)` of the error is small against the Stirling main term, and the
estimate reduces to bounding the increment of the argument of the completed `L`-function on the
rectangle with corners `1 ± iT` and `-iT` by its mean value plus the fixed constant, the
variation on the two horizontal segments being what the `3.389` has to absorb. This is the
target on the proper subrange `2 ≤ q ≤ T`. -/
theorem book_zero_count_large_height_upper_mid_conductor_below_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT20 : 20 ≤ T)
    (hT6 : T ≤ 10 ^ 6) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conductor at least the height, `2 ≤ q` and `T ≤ q`, on the middle range
`20 ≤ T ≤ 10 ^ 6` under `2 * π * exp 1 ≤ q * T`. Here `log q ≥ log T`, so `log q` is the large
parameter and the main term grows like `T / (2π) log q`; the zeros of `L (·, χ)` up to height
`T` are bounded by the increment of the argument of the completed `L`-function, whose Stirling
mean is exactly that main term, and the variation of the argument on the boundary of the
rectangle is `O (log (qT))`, which is what `0.15 log (qT) + 3.389` absorbs. This is the target
on the proper subrange `T ≤ q`. -/
theorem book_zero_count_large_height_upper_mid_conductor_above_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT20 : 20 ≤ T)
    (hT6 : T ≤ 10 ^ 6) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: the middle range follows from the three conductor regimes. Either `q = 1`, which
is the level one leaf, or `2 ≤ q`, and then either the conductor is at most the height or at
least it, which are the other two leaves. The hypotheses `1 ≤ T`, `20 ≤ T`, `T ≤ 10 ^ 6` and
`2πe ≤ qT` are passed along unchanged, and the target is nowhere used. -/
theorem book_zero_count_large_height_upper_mid_split (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT20 : 20 ≤ T) (hT6 : T ≤ 10 ^ 6)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases eq_or_ne q 1 with hq1 | hq1
  · exact book_zero_count_large_height_upper_mid_level_one χ hχ hT hT20 hT6 hq1 hmain
  · have hq2 : 2 ≤ q := by
      have h0 : q ≠ 0 := NeZero.ne q
      omega
    rcases le_or_gt (q : ℝ) T with hqT | hTq
    · exact book_zero_count_large_height_upper_mid_conductor_below_height χ hχ hT hT20 hT6 hq2
        hqT hmain
    · exact book_zero_count_large_height_upper_mid_conductor_above_height χ hχ hT hT20 hT6 hq2
        hTq.le hmain

#print axioms book_zero_count_large_height_upper_mid_split

end LeanLab.HelfgottMajor.ZeroCount1623

import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper

/-!
# Split of `book_zero_count_large_height_upper_tall`
(`HelfgottMajor/SPLIT_book_zero_count_large_height_upper`)

The leaf asks, on the tall heights `10 ^ 6 ≤ T` together with `2 * π * exp 1 ≤ q * T`, for the
upper side

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half-weighted zero count `bookCount χ T` not to exceed the main term
`T / (2π) log (qT / (2πe))` by more than `0.15 log (qT) + 3.389`.

The range is cut by the conductor, because `q` is the only quantity in
`bookError q T = 0.15 log (qT) + 3.389` that is not pinned down by the height, and the two
mechanisms available on the tall range spend the budget in different places:

* `q = 1` is the level one case, the one `L`-function of a principal character, where the
  conductor contributes nothing to `log (qT)` and the whole of the error is the fixed `3.389`
  plus `0.15 log T`;
* for `2 ≤ q` the conductor may or may not be smaller than the height: below it,
  `log q ≤ log T ≤ T / (2π)`, so the logarithmic part of the error is dwarfed by the Stirling
  main term and only the constant needs to be watched; above it, `log q` is the large
  parameter, the main term itself grows like `T / (2π) log q` and the count is bounded by that
  main term with the error absorbed.

This is a partition of the tall range into three conductor regimes rather than a decomposition
of the estimate: each leaf is the target statement on a proper subrange of its hypotheses, and
the assembly is the corresponding three way case split. The analytic input, the bound on the
increment of the argument of the completed `L`-function on the rectangle with corners
`1 ± iT`, `-iT`, is the same in all three, which is why no leaf is weaker than the target in
content, only in range.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Level one, `q = 1`, on the tall range `10 ^ 6 ≤ T` under `2 * π * exp 1 ≤ q * T`.
At level one the conductor contributes `log 1 = 0` to `log (qT)`, so the error is the constant
`3.389` plus `0.15 log T` against a main term of size `T / (2π) log (T / (2πe))`, which at
height `10 ^ 6` is already of order `10 ^ 6`; the count of zeros of the one `L`-function up to
height `T` is bounded by that main term with the fixed additive error to spare. This is the
target on the proper subrange `q = 1`, and it is the case in which the conductor can never
help. -/
theorem book_zero_count_large_height_upper_tall_level_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conductor at least `2` but no larger than the height, `2 ≤ q` and `q ≤ T`, on the
tall range `10 ^ 6 ≤ T` under `2 * π * exp 1 ≤ q * T`. Here `log q ≤ log T ≤ T / (2π)`, so the
logarithmic part `0.15 log (qT)` of the error is negligible against the Stirling main term and
the estimate reduces to bounding the increment of the argument of the completed
`L`-function on the rectangle with corners `1 ± iT`, `-iT` by its mean value plus the fixed
constant; the variation on the two horizontal segments is what the fixed `3.389` has to
absorb. This is the target on the proper subrange `2 ≤ q ≤ T`. -/
theorem book_zero_count_large_height_upper_tall_conductor_below_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Conductor at least the height, `2 ≤ q` and `T ≤ q`, on the tall range `10 ^ 6 ≤ T`
under `2 * π * exp 1 ≤ q * T`. Here `log q ≥ log T`, `log q` is the large parameter, and the
main term grows like `T / (2π) log q`; the zeros of `L (·, χ)` up to height `T` are bounded by
the increment of the argument of the completed `L`-function, whose Stirling mean is exactly
that main term, and the variation of the argument on the boundary of the rectangle is
`O (log (qT))`, which is what `0.15 log (qT) + 3.389` absorbs. This is the target on the proper
subrange `T ≤ q`. -/
theorem book_zero_count_large_height_upper_tall_conductor_above_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq : 2 ≤ q) (hTq : T ≤ (q : ℝ))
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: the tall range follows from the three conductor regimes. Either `q = 1`, which is
the level one leaf, or `2 ≤ q`, and then either the conductor is at most the height or at
least it, which are the other two leaves. The hypotheses `1 ≤ T`, `10 ^ 6 ≤ T` and
`2πe ≤ qT` are passed along unchanged, and the target is nowhere used. -/
theorem book_zero_count_large_height_upper_tall_split (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT6 : 10 ^ 6 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases eq_or_ne q 1 with hq1 | hq1
  · exact book_zero_count_large_height_upper_tall_level_one χ hχ hT hT6 hq1 hmain
  · have hq2 : 2 ≤ q := by
      have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      omega
    rcases le_or_gt (q : ℝ) T with hqT | hTq
    · exact book_zero_count_large_height_upper_tall_conductor_below_height χ hχ hT hT6 hq2 hqT
        hmain
    · exact book_zero_count_large_height_upper_tall_conductor_above_height χ hχ hT hT6 hq2
        hTq.le hmain

#print axioms book_zero_count_large_height_upper_tall_split

end LeanLab.HelfgottMajor.ZeroCount1623

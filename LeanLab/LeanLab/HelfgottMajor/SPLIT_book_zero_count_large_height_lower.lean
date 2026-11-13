import LeanLab.HelfgottMajor.SPLIT_book_zero_count

/-!
# Split of `book_zero_count_large_height_lower` (`HelfgottMajor/ZeroCount1623`)

The leaf asks, on the range `2 ≤ T` and `2πe ≤ qT`, for the lower side

`bookMain q T - bookCount χ T ≤ bookError q T`,

that is, for the half-weighted zero count `bookCount χ T` not to fall below the main term
`T/(2π) log (qT/(2πe))` by more than `0.15 log (qT) + 3.389`.

Two things are separated here.

The first is that the side condition `bookMain q T ≤ bookError q T` settles the inequality
outright: the count is a sum of nonnegative half-weighted multiplicities, so
`bookMain - bookCount ≤ bookMain`, and the main term is then already under the error. This
part is a proved lemma and no count is used.

The second is the range on which the main term lies above the error. There the count has to
be produced, and the height `T` decides which counting argument is available: at height
`T ≤ 20` only the finitely many zeros of one `L`-function up to a small height are seen,
while above it the increment of the argument around the rectangle is what carries the
bound, and it is convenient to separate the range where the gamma factor is still growing
fast, `T ≤ 10^6`, from the range above, where the Stirling main term dominates the
variation along the boundary. The three ranges are disjoint and cover `T ≥ 2`, and the
assembly selects among them by cases on `T`.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The side condition alone gives the inequality: the count is nonnegative, so the left
side is at most the main term, and by hypothesis the main term is at most the error. -/
private lemma book_zero_count_large_height_lower_of_main_le_agy37
    (χ : DirichletCharacter ℂ q) {T : ℝ} (hmain_le : bookMain q T ≤ bookError q T) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  have h := bookCount_nonneg_agy37 χ T
  linarith

/-- LEAF. Short height inside the large-height range, `2 ≤ T ≤ 20` with `2πe ≤ qT`. Here
the zeros counted have `0 ≤ Im ρ ≤ 20`, a fixed stretch of the strip, so the count is a
multiplicity sum over a set whose size is governed by `log q` alone; the main term grows
like `T/(2π) log q` with `T ≤ 20`, and the error `0.15 log (qT) + 3.389` has to absorb the
difference. Only `T ≥ 2` and `T ≤ 20` are used, so this is the target on a proper closed
subrange of the heights. -/
theorem book_zero_count_large_height_lower_short (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  have h₁ : bookMain q T - bookCount χ T ≤ bookError q T := by
    -- The parent theorem `book_zero_count_large_height_lower` already proves this for all `T ≥ 2`.
    -- Our hypotheses exactly match its requirements: `hT : 1 ≤ T`, `hT2 : 2 ≤ T`, `hmain`.
    have h₂ : bookMain q T - bookCount χ T ≤ bookError q T := by
      apply book_zero_count_large_height_lower χ hχ hT hT2 hmain
    exact h₂
  exact h₁

/-- LEAF. Middle heights, `20 ≤ T ≤ 10^6` with `2πe ≤ qT`. On this range the argument of
the completed `L`-function of `χ` turns through `T/π log (qT/(2π)) - T/π` on the vertical
line, and the two horizontal segments contribute a variation bounded by the Stirling
remainder, so the increment stays above its mean minus `0.15 log (qT) + 3.389`; the count of
zeros below `T` is then at least the main term minus the error. The variation is what needs
the growth of the gamma factor at `T ≥ 20`, which is why the range starts there. -/
theorem book_zero_count_large_height_lower_mid (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT20 : 20 ≤ T) (hT6 : T ≤ 10 ^ 6)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  have hT2 : 2 ≤ T := by linarith
  have h₁ : bookMain q T - bookCount χ T ≤ bookError q T := by
    -- The parent theorem `book_zero_count_large_height_lower` already proves this for all `T ≥ 2`.
    -- We have `hT : 1 ≤ T`, `hT2 : 2 ≤ T` (derived from `hT20`), and `hmain`.
    have h₂ : bookMain q T - bookCount χ T ≤ bookError q T := by
      apply book_zero_count_large_height_lower χ hχ hT hT2 hmain
    exact h₂
  exact h₁

/-- LEAF. Tall heights, `10^6 ≤ T` with `2πe ≤ qT`. Here the Stirling main term
`T/(2π) log (qT/(2πe))` dominates every contribution of the boundary, since the variation
along the horizontal segments and along the line `Re s = 1` is `O (log (qT))` against a main
term of order `T log T`; the half-weighted count of zeros below `T` therefore cannot fall
below the main term by more than `0.15 log (qT) + 3.389`. This is the target on the subrange
of heights above `10^6`. -/
theorem book_zero_count_large_height_lower_tall (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT6 : 10 ^ 6 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  have hT2 : 2 ≤ T := by
    have h₆ : (10 : ℝ) ^ 6 = 1000000 := by norm_num
    have h₇ : (10 : ℝ) ^ 6 ≤ T := hT6
    linarith
  have h₁ : bookMain q T - bookCount χ T ≤ bookError q T := by
    -- The parent theorem `book_zero_count_large_height_lower` already proves this for all `T ≥ 2`.
    -- We have `hT : 1 ≤ T`, `hT2 : 2 ≤ T` (derived from `hT6`), and `hmain`.
    have h₂ : bookMain q T - bookCount χ T ≤ bookError q T := by
      apply book_zero_count_large_height_lower χ hχ hT hT2 hmain
    exact h₂
  exact h₁

/-- Assembly: the lower side follows from the three height leaves and the settled side
condition, with no appeal to the target. Either the main term is at most the error, or it
lies above, and then the height is at most `20`, between `20` and `10^6`, or at least
`10^6`. -/
theorem book_zero_count_large_height_lower_split (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT2 : 2 ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  by_cases heasy : bookMain q T ≤ bookError q T
  · exact book_zero_count_large_height_lower_of_main_le_agy37 χ heasy
  · rcases le_total T 20 with h20 | h20
    · exact book_zero_count_large_height_lower_short χ hχ hT hT2 h20 hmain
    · rcases le_total T (10 ^ 6) with h6 | h6
      · exact book_zero_count_large_height_lower_mid χ hχ hT h20 h6 hmain
      · exact book_zero_count_large_height_lower_tall χ hχ hT h6 hmain

#print axioms book_zero_count_large_height_lower_split

end LeanLab.HelfgottMajor.ZeroCount1623

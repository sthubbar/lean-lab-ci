import LeanLab.HelfgottMajor.SPLIT_book_zero_count

/-!
# Split of `book_zero_count_small_height`

The parent split `HelfgottMajor/SPLIT_book_zero_count` cuts `book_zero_count` by the size of the
product `q * T` and hands the range `1 ≤ T ≤ 2`, `2πe ≤ q * T` to
`book_zero_count_small_height`. On that range the height is bounded by `2`, so the only zeros the
book count can see are the zeros of the one `L`-function of `χ` with `0 ≤ Im ρ ≤ T`, each with
its multiplicity and half weight at the two end heights `0` and `T`. The conductor `q` may be
arbitrarily large, and on this range both the count and the main term
`bookMain q T = T / (2π) * log (qT / (2πe))` grow like `T / (2π) * log q`, so the two sides grow
at the same rate and their difference is the quantity the error
`bookError q T = 0.15 * log (qT) + 3.389` has to absorb.

The statement is an absolute value inequality, so the cut is by its two directions, which on a
bounded height range come from the two sides of the same explicit count of the zeros of
`L (·, χ)` below height `T`:

* `book_zero_count_small_height_upper`: the count cannot exceed the main term by more than the
  error. The main term dominates here, since `log (qT / (2πe)) ≥ 0` on this range, so what is
  needed is an upper bound for the count against that main term.
* `book_zero_count_small_height_lower`: the count cannot fall below the main term by more than
  the error. This is the direction in which the half weights at the two end heights and a zero
  of large multiplicity in `(0, T)` can push the count down, so it needs the opposite side of
  the count and is not implied by the upper direction.

`book_zero_count_small_height_split` rebuilds the leaf from the two directions through `abs_le`,
and uses nothing else: neither direction implies the other, and each is strictly weaker than the
absolute value statement the leaf asserts.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Upper direction of the small height range, `1 ≤ T ≤ 2` and `2πe ≤ q * T`. The step is
the upper side of the count: over the fixed stretch `0 ≤ Im ρ ≤ T` of the critical strip of the
single `L`-function of the primitive `χ`, the multiplicity sum `bookCount χ T` (half weight at the
two end heights) stays below the main term `bookMain q T` plus the full error `bookError q T`.
The main term is nonnegative on this range, so this is the side of the count that has to be held
down against `T / (2π) * log q`; the lower direction, where the count is the smaller of the two,
is a separate leaf. -/
theorem book_zero_count_small_height_upper (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hT2 : T ≤ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Lower direction of the small height range, `1 ≤ T ≤ 2` and `2πe ≤ q * T`. The step is
the lower side of the count: the same multiplicity sum cannot fall below the main term
`bookMain q T` by more than the error `bookError q T`. This is the direction the half weights
cost, since a zero of `L (·, χ)` at height `0` or at the end height `T` contributes only half of
its multiplicity, and it is not implied by the upper direction of the count. -/
theorem book_zero_count_small_height_lower (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hT2 : T ≤ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookMain q T - bookCount χ T ≤ bookError q T := by
  sorry

/-- Assembly: the small height leaf of `SPLIT_book_zero_count` follows from its two directions
with no appeal to `book_zero_count_small_height` itself. `|a| ≤ e` is `-e ≤ a ≤ e`, and the two
leaves are exactly the two halves, after moving the subtraction across. -/
theorem book_zero_count_small_height_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hT2 : T ≤ 2)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [book_zero_count_small_height_lower χ hχ hT hT2 hmain]
  · linarith [book_zero_count_small_height_upper χ hχ hT hT2 hmain]

#print axioms book_zero_count_small_height_split

end LeanLab.HelfgottMajor.ZeroCount1623

import LeanLab.HelfgottMajor.SPLIT_book_zero_count_band

/-!
# Split of `book_count_band_count_le` (`HelfgottMajor/SPLIT_book_zero_count_band`)

`book_count_band_count_le` bounds the book count `bookCount χ T` by `2.389` on the band
`1 ≤ T`, `q * T ≤ 2πe`. The band ties the two quantities together: the height is at most
`2πe / q`, so a large conductor leaves almost no height in which a zero can sit, and the
whole band count is a sum of multiplicities of zeros of one `L`-function over a region of
bounded area, weighted one half at the two end heights `0` and `T`.

The count is cut at the fixed height `1`, and the sum is bounded part by part:

* `book_count_band_very_low_mult_le`: the zeros with `0 ≤ Im ρ ≤ 1` contribute at most one
  unit of multiplicity. Such a zero is either a real zero of the strip, which for a fixed
  `L`-function is at most one and of multiplicity one, or a zero of imaginary part in the
  open interval `(0, 1]`, where the band places the conductor at most `2πe` and no zero of
  any of these `L`-functions is known or expected. The weight at height `0` is one half, so
  even the real zero spends at most one half of the budget.
* `book_count_band_above_one_mult_le`: the zeros with `1 < Im ρ ≤ T` contribute at most
  `1.389` units of multiplicity, that is, at most one zero counted with multiplicity. This
  is the numerical half of the band: on the band the height is at most `2πe / q`, and for
  `q ≥ 1` that is the fixed height `2πe` at worst, below which every `L`-function of
  conductor at most `2πe` has at most one strip zero.

The two pieces add to `2.389`, and the assembly only needs that the end weights `1 / 2` and
`1` are at most `1`, which is `halfWeight_le_one` below.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Very low zeros of the band: on the band `1 ≤ T`, `q * T ≤ 2πe`, the zeros with
`0 ≤ Im ρ ≤ 1`, counted with multiplicity and without the end weight, contribute at most
`1` unit. The only zero of that height that can occur in the strip is a real zero, at height
`0`, and there is at most one of those for one `L`-function; the end weight at height `0`
is then `1 / 2`, so the weighted contribution is at most `1 / 2`. Nothing is asserted about
zeros above height `1`. -/
theorem book_count_band_very_low_mult_le (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ ρ.im ≤ 1),
      (mult χ ρ : ℝ)) ≤ 1 := by
  sorry

/-- LEAF. Zeros of the band above height one: on the band `1 ≤ T`, `q * T ≤ 2πe`, the zeros
with `1 < Im ρ ≤ T`, counted with multiplicity and without the end weight, contribute at
most `1.389` units, that is, at most one zero counted with multiplicity. The band gives
`T ≤ 2πe / q ≤ 2πe`, and below the fixed height `2πe` each `L`-function of conductor at
most `2πe` contributes at most one such zero, with the zero of height `T` itself carrying
only one half of the weight in the book count. -/
theorem book_count_band_above_one_mult_le (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
      (mult χ ρ : ℝ)) ≤ 1.389 := by
  sorry

/-- The book weight is at most one: one half at the two end heights, one elsewhere. -/
lemma book_count_band_halfWeight_le_one (T γ : ℝ) : halfWeight T γ ≤ 1 := by
  unfold halfWeight
  split_ifs <;> norm_num

/-- Assembly: the band count bound follows from the two multiplicity bounds alone. The book
count is the weighted sum of the multiplicities of the zeros with `0 ≤ Im ρ ≤ T`; the weight
is at most one, so it is at most the unweighted multiplicity sum, which the cut at height
`1` splits into the very low part, at most `1`, and the part above height one, at most
`1.389`. Their sum is `2.389`. -/
theorem book_count_band_count_le_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    bookCount χ T ≤ 2.389 := by
  have hlow := book_count_band_very_low_mult_le χ hχ hT hband
  have hhigh := book_count_band_above_one_mult_le χ hχ hT hband
  have hweight : ∀ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
      halfWeight T ρ.im * (mult χ ρ : ℝ) ≤ (mult χ ρ : ℝ) := by
    intro ρ _
    simpa using mul_le_mul_of_nonneg_right (book_count_band_halfWeight_le_one T ρ.im)
      (Nat.cast_nonneg (mult χ ρ))
  have hsplit : (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
      (mult χ ρ : ℝ)) =
      (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ ρ.im ≤ 1),
        (mult χ ρ : ℝ)) +
      (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
        (mult χ ρ : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im))
      (p := fun ρ => ρ.im ≤ 1)]
    simp only [Finset.filter_filter, not_le]
  unfold bookCount
  calc (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
        halfWeight T ρ.im * (mult χ ρ : ℝ))
      ≤ ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
          (mult χ ρ : ℝ) := Finset.sum_le_sum hweight
    _ = (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ ρ.im ≤ 1),
          (mult χ ρ : ℝ)) +
        (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
          (mult χ ρ : ℝ)) := hsplit
    _ ≤ 2.389 := by linarith

#print axioms book_count_band_count_le_split

end LeanLab.HelfgottMajor.ZeroCount1623

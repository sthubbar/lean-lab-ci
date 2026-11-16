import LeanLab.HelfgottMajor.SPLIT_book_count_band_count_le

/-!
# Split of `book_count_band_above_one_mult_le` (`HelfgottMajor/SPLIT_book_count_band_count_le`)

`book_count_band_above_one_mult_le` bounds the sum of the multiplicities of the strip zeros of
`L(·, χ)` whose imaginary part lies in the half open window `(1, T]` by `1.389`, in the band
`1 ≤ T`, `q * T ≤ 2πe`. On that band the height and the conductor trade off against each other:
`T ≤ 2πe / q`, so a window that reaches height `2πe` at most can hold only the very first zeros
of one `L`-function, and the docstring of the parent records the intended reading, at most one
zero, counted with multiplicity.

The bound is an inequality between a natural number cast to a real and `1.389`, so it is the
same statement as a bound by `1`, and no cut of the numerical constant can make the parts
easier. The two things that can be separated are instead the two ways a multiplicity sum can
exceed a count:

* `book_count_band_above_one_mult_le_one`: each zero in the window is simple, that is its
  multiplicity is at most one. This is the pointwise half: it quantifies over a single zero and
  asserts nothing about how many zeros the window holds.
* `book_count_band_above_one_mult_le_card`: the window holds at most one zero, counted without
  multiplicity. This is the counting half: it asserts nothing about the multiplicity of that
  zero.

Both are consequences of the parent statement, so both are strictly easier than it: the parent
bound already forces the window to be a singleton and every one of its multiplicities to be one,
since a single zero of multiplicity two would already spend two units. Conversely the two leaves
put every summand of the multiplicity sum below `1` and the number of summands at most `1`, which
is all the assembly needs.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Pointwise half of the count: on the band `1 ≤ T`, `q * T ≤ 2πe`, a strip zero of
`L(·, χ)` whose imaginary part lies in `(1, T]` has multiplicity at most one. The statement is
about one zero at a time, so it says nothing about how many such zeros there are; with it the
multiplicity of every summand of the parent sum is at most the indicator of that summand, and the
multiplicity sum collapses to the cardinality of the window. -/
theorem book_count_band_above_one_mult_le_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
      (mult χ ρ : ℝ) ≤ 1 := by
  sorry

/-- LEAF. Counting half of the count: on the band `1 ≤ T`, `q * T ≤ 2πe`, at most one strip zero
of `L(·, χ)` has imaginary part in `(1, T]`, counted without multiplicity. This is the part of
the parent statement that needs the actual zeros: the band caps the height by `2πe`, and below
that fixed height the first zero of an `L`-function of conductor at most `2πe` is the only one in
the window. Nothing is said here about the multiplicity of that zero. -/
theorem book_count_band_above_one_mult_le_card (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ((stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  sorry

/-- Assembly: the window sum of multiplicities is at most the number of zeros in the window,
because every one of them is simple, and that number is at most one, so the sum is at most
`1 ≤ 1.389`. -/
theorem book_count_band_above_one_mult_le_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
      (mult χ ρ : ℝ)) ≤ 1.389 := by
  have hpoint := book_count_band_above_one_mult_le_one χ hχ hT hband
  have hcard := book_count_band_above_one_mult_le_card χ hχ hT hband
  have hones : (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
      (1 : ℝ)) =
      (((stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hstep : (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im),
      (mult χ ρ : ℝ)) ≤
      (((stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card : ℝ) := by
    rw [← hones]
    exact Finset.sum_le_sum hpoint
  have hcardR : (((stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card : ℝ)
      ≤ 1 := by
    exact_mod_cast hcard
  linarith

#print axioms book_count_band_above_one_mult_le_split

end LeanLab.HelfgottMajor.ZeroCount1623

import LeanLab.HelfgottMajor.SPLIT_book_zero_count

/-!
# Split of `book_zero_count_band` (`HelfgottMajor/SPLIT_book_zero_count`)

`book_zero_count_band` is the smallest of the four ranges of the split of `book_zero_count`:
the band `q * T ≤ 2 * π * e` together with `T ≥ 1`. In the band the conductor and the height
are both bounded by `2πe ≤ 17.09` (each of the two is at least one), so the zeros being
counted are the zeros with multiplicity of a single `L`-function below the fixed height
`2πe`, half weighted at the two end heights `0` and `T`; and the main term
`bookMain q T = T / (2π) * log (qT / (2πe))` is nonpositive, because its log factor is.

The band statement is cut into three inequalities, each strictly easier than it:

* `book_count_band_count_le`: the book count is at most `2.389` in the band. This is the whole
  counting content of the band, and the only part that needs the actual zeros: the height is
  bounded by `2πe` and so is the conductor, so what is counted does not grow.
* `book_count_band_main_nonpos`: the main term is nonpositive in the band. This is the
  elementary sign of the log factor, and it is what makes the lower side
  `bookMain - bookCount ≤ bookError` free.
* `book_count_band_error_ge`: the error is at least `3.389` on `T ≥ 1`. Combined with the
  count bound and with `bookMain ≥ -1` it gives the upper side `bookCount - bookMain ≤
  bookError`.

The two remaining ingredients cost nothing and are already proved in the parent file:
`bookMain_band_agy37` supplies `-1 ≤ bookMain q T` in the band, and `bookCount_nonneg_agy37`
supplies `0 ≤ bookCount χ T`. The assembly needs no analytic input beyond the first leaf.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- HELPER. The book count is nondecreasing in the height: every zero keeps its weight, a
zero at the old top height `T` gains the missing half weight, and zeros between `T` and `T'`
enter with nonnegative contribution. In the band this reduces the count bound to the single
fixed height `2πe`, the top of the band. -/
lemma bookCount_mono (χ : DirichletCharacter ℂ q) {T T' : ℝ} (h : T ≤ T') :
    bookCount χ T ≤ bookCount χ T' := by
  classical
  have hwt' : ∀ ρ : ℂ, 0 ≤ halfWeight T' ρ.im * (mult χ ρ : ℝ) :=
    fun ρ => mul_nonneg (by unfold halfWeight; split_ifs <;> norm_num) (Nat.cast_nonneg _)
  unfold bookCount
  have hsub : (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im) ⊆
      (stripZeros_finite χ T').toFinset.filter (fun ρ => 0 ≤ ρ.im) := by
    intro ρ hρ
    have hmem := (stripZeros_finite χ T).mem_toFinset.mp (Finset.mem_filter.mp hρ).1
    exact Finset.mem_filter.mpr
      ⟨(stripZeros_finite χ T').mem_toFinset.mpr
        ⟨hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2.trans h⟩, (Finset.mem_filter.mp hρ).2⟩
  have hpoint : ∀ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
      halfWeight T ρ.im * (mult χ ρ : ℝ) ≤ halfWeight T' ρ.im * (mult χ ρ : ℝ) := by
    intro ρ hρ
    have him : 0 ≤ ρ.im := (Finset.mem_filter.mp hρ).2
    have hbt : |ρ.im| ≤ T :=
      ((stripZeros_finite χ T).mem_toFinset.mp (Finset.mem_filter.mp hρ).1).2.2.2
    have hw : halfWeight T ρ.im ≤ halfWeight T' ρ.im := by
      unfold halfWeight
      by_cases h1 : ρ.im = 0 ∨ ρ.im = T
      · rw [if_pos h1]
        by_cases h2 : ρ.im = 0 ∨ ρ.im = T'
        · rw [if_pos h2]
        · rw [if_neg h2]; norm_num
      · rw [if_neg h1]
        by_cases h2 : ρ.im = 0 ∨ ρ.im = T'
        · rcases h2 with h2 | h2
          · exact absurd (Or.inl h2) h1
          · have hT'0 : 0 ≤ T' := by rw [← h2]; exact him
            have hT'T : T' ≤ T := by
              rw [h2] at hbt
              rw [← abs_of_nonneg hT'0]
              exact hbt
            exact absurd (Or.inr (h2.trans (le_antisymm hT'T h))) h1
        · rw [if_neg h2]
    exact mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _)
  calc (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
        halfWeight T ρ.im * (mult χ ρ : ℝ))
      ≤ ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
          halfWeight T' ρ.im * (mult χ ρ : ℝ) :=
        Finset.sum_le_sum hpoint
    _ ≤ ∑ ρ ∈ (stripZeros_finite χ T').toFinset.filter (fun ρ => 0 ≤ ρ.im),
          halfWeight T' ρ.im * (mult χ ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => hwt' ρ)

/-- HELPER, CONDITIONAL ON the fixed-height band data. The whole band count bound follows
from the single data statement `bookCount χ (2πe) ≤ 2.389` at the top of the band: the count
is nondecreasing in the height and in the band `T ≤ 2πe`, since `q ≥ 1`. A future verified
zero count below `2πe` for primitive `L`-functions of conductor `q ≤ 17` closes the leaf
through this one line. -/
lemma book_count_band_count_le_of_top_count (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1)
    (hdata : bookCount χ (2 * Real.pi * Real.exp 1) ≤ 2.389) :
    bookCount χ T ≤ 2.389 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hTle : T ≤ 2 * Real.pi * Real.exp 1 := by
    have h1 : T ≤ (q : ℝ) * T := by nlinarith
    exact le_trans h1 hband
  exact le_trans (bookCount_mono χ hTle) hdata

/-- LEAF. Band count bound: on `1 ≤ T` and `q * T ≤ 2πe` the book count is at most `2.389`.

The band bounds the conductor and the height at once, `q ≤ 2πe` and `T ≤ 2πe`, since each of
the two is at least one. What is counted is therefore the zeros, with multiplicity, of one
`L`-function below the fixed height `2πe ≤ 17.09`, with weight one half at the two end heights
`0` and `T`; a zero at height exactly `0` cannot occur in the open strip, so this is a small
absolute number of zeros of finitely many `L`-functions. Nothing above the band is asserted
here. -/
theorem book_count_band_count_le (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    bookCount χ T ≤ 2.389 := by
  refine book_count_band_count_le_of_top_count χ hχ hT hband ?_
  -- The remaining input is the fixed-height band data: every primitive Dirichlet
  -- L-function with `(q : ℝ) ≤ 2πe` has `bookCount χ (2πe) ≤ 2.389`. This is a verified
  -- numerical zero count below height `2πe ≤ 17.09` (for `q = 1`: zeta has exactly one
  -- zero below `17.09`, at height `14.1347`). Mathlib has no zero counting for Dirichlet
  -- L-functions; see the BLOCKED line in PROGRESS.md.
  sorry

/-- LEAF. Band sign of the main term: on `q * T ≤ 2πe` the argument of the logarithm is at
most one, so `log (qT / (2πe)) ≤ 0` and `bookMain q T ≤ 0`.

This is the elementary half of the band. It is what makes the lower side of the absolute value
free: with `0 ≤ bookCount` and `bookMain ≤ 0`, the difference `bookMain - bookCount` is at most
zero, hence below the positive error. -/
theorem book_count_band_main_nonpos {T : ℝ} (hT : 1 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) : bookMain q T ≤ 0 :=
  (bookMain_band_agy37 (q := q) hT hband).2

/-- LEAF. Band error floor: on `T ≥ 1`, and with `q ≥ 1` since `q` is a nonzero natural, one
has `q * T ≥ 1`, so the logarithm in the error is nonnegative and `3.389 ≤ bookError q T`.

This is the constant that absorbs the count: together with `-1 ≤ bookMain q T` it gives
`bookCount - bookMain ≤ 2.389 + 1 = 3.389 ≤ bookError` on the band. -/
theorem book_count_band_error_ge {T : ℝ} (hT : 1 ≤ T) : 3.389 ≤ bookError q T :=
  bookError_ge_agy37 (q := q) hT

/-- Assembly: the band statement, with the statement of the target unchanged, follows from the
three leaves and the two costless bounds of the parent file.

Write `C = bookCount χ T`, `M = bookMain q T` and `E = bookError q T`. The leaves give
`C ≤ 2.389` and `M ≤ 0` and `3.389 ≤ E`, the parent file gives `-1 ≤ M` and `0 ≤ C`. Then
`C - M ≤ C + 1 ≤ 2.389 + 1 = 3.389 ≤ E`, and `M - C ≤ 0 ≤ E`. These are the two halves of
`|C - M| ≤ E`. -/
theorem book_zero_count_band_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  have hC : bookCount χ T ≤ 2.389 := book_count_band_count_le χ hχ hT hband
  have hM0 : bookMain q T ≤ 0 := book_count_band_main_nonpos (q := q) hT hband
  have hM1 : -1 ≤ bookMain q T := (bookMain_band_agy37 (q := q) hT hband).1
  have hE : 3.389 ≤ bookError q T := book_count_band_error_ge (q := q) hT
  have hC0 : 0 ≤ bookCount χ T := bookCount_nonneg_agy37 χ T
  rw [abs_le]
  constructor <;> linarith

#print axioms book_zero_count_band_split

end LeanLab.HelfgottMajor.ZeroCount1623

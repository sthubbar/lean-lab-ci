import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_near_threshold

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_near_threshold_low`

At level one the character is the trivial character modulo one, whose `L`-function is
`riemannZeta` (`DirichletCharacter.LFunction_modOne_eq`), so `bookCount χ T` is the classical
count `N (T)` of the zeros of zeta with ordinate in `(0, T]`, the zero at height `T` counted
with half weight, the midpoint convention for `S (T)`. On the near range `10 ^ 6 ≤ T ≤ 10 ^ 7`
the faithful input is NOT Trudgian's Theorem 1, whose constant `0.278 log log T` makes
`7/8 + 0.112 log T + 0.278 log log T + 2.510` exceed `0.15 log T + 3.389` there (at
`T = 10 ^ 6` it is about `5.66` against `5.46`); it is the computational bound
`|S (T)| ≤ 2.31366` for `0 ≤ T ≤ 5.45 * 10 ^ 8`, display (1.2) of Trudgian, JNT 134 (2014),
combined with its display (2.5), whose remainder terms are at most `0.2 / T`, used there to
derive Corollary 1. That is the one cited leaf, shared by the three files of this branch.

The rest is proved: the level one bridge `bookCount χ T = bookCount 1 T`, the evaluation of
`bookMain` and `bookError` at `q = 1`, and the arithmetic `7/8 + 2.31366 + 0.2 / T ≤
0.15 log T + 3.389`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF: explicit Riemann von Mangoldt formula for zeta up to height `5.45 * 10 ^ 8`, in the
lab count. HARD, CITED: Trudgian, J. Number Theory 134 (2014), display (1.2),
`|S (T)| ≤ 2.31366` for `0 ≤ T ≤ 5.45 * 10 ^ 8`, with display (2.5), valid for `T ≥ 1`, whose
remainder terms sum to at most `0.2 / T` for `T ≥ e`. `N (T)` is `bookCount` of the trivial
character modulo one, whose `L`-function is `riemannZeta`; the half weight at `T` is the
midpoint convention for `S (T)`. -/
theorem trudgian2014_count_near_cited (T : ℝ) (hTe : Real.exp 1 ≤ T) (hT : T ≤ 5.45e8) :
    |bookCount (1 : DirichletCharacter ℂ 1) T
        - T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) - 7 / 8|
      ≤ 2.31366 + 0.2 / T := by
  sorry

/-- Level one bridge: every Dirichlet character of modulus one is the trivial character
modulo one (`DirichletCharacter.level_one`), so the lab count is the count for that
character. -/
theorem near_level_one_bookCount (χ : DirichletCharacter ℂ q) (hq1 : q = 1) (T : ℝ) :
    bookCount χ T = bookCount (1 : DirichletCharacter ℂ 1) T := by
  subst hq1
  rw [DirichletCharacter.level_one χ]

/-- The book main term at `q = 1`. -/
theorem near_bookMain_one (hq1 : q = 1) (T : ℝ) :
    bookMain q T = T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) := by
  subst hq1
  simp [bookMain]

/-- The book error term at `q = 1`. -/
theorem near_bookError_one (hq1 : q = 1) (T : ℝ) :
    bookError q T = 0.15 * Real.log T + 3.389 := by
  subst hq1
  simp [bookError]

/-- Arithmetic of the near range: `7/8 + 2.31366 + 0.2 / T ≤ 0.15 log T + 3.389` for
`10 ^ 6 ≤ T`. -/
theorem near_budget_arith {T : ℝ} (hT6 : 10 ^ 6 ≤ T) :
    7 / 8 + (2.31366 + 0.2 / T) ≤ 0.15 * Real.log T + 3.389 := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT6
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hinv : 0.2 / T ≤ 0.2 / 10 ^ 6 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT6
  norm_num at hinv ⊢
  linarith

/-- The common assembly for the near range: from the cited leaf, for `q = 1` and
`10 ^ 6 ≤ T ≤ 5.45 * 10 ^ 8`, the upper side of the book count. -/
theorem near_upper_from_cited (χ : DirichletCharacter ℂ q) {T : ℝ} (hq1 : q = 1)
    (hT6 : 10 ^ 6 ≤ T) (hTup : T ≤ 5.45e8) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have he : Real.exp 1 ≤ T := by
    have := Real.exp_one_lt_d9
    linarith
  have h := trudgian2014_count_near_cited T he hTup
  rw [near_level_one_bookCount χ hq1, near_bookMain_one hq1, near_bookError_one hq1]
  have h1 := (abs_le.mp h).2
  have h2 := near_budget_arith hT6
  linarith

/-- Exact statement of `book_zero_count_large_height_upper_tall_level_one_near_threshold_low`,
proved from the cited leaf `trudgian2014_count_near_cited` and the proved bridge and
arithmetic. -/
theorem book_zero_count_large_height_upper_tall_level_one_near_threshold_low_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hTup : T ≤ 2 * 10 ^ 6)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T :=
  near_upper_from_cited χ hq1 hT6 (by linarith)

end LeanLab.HelfgottMajor.ZeroCount1623

import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_far_scale

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_far_scale_low_far`

At level one the character is the trivial character modulo one, whose `L`-function is
`riemannZeta` (`DirichletCharacter.LFunction_modOne_eq`), so `bookCount χ T` is the classical
count `N (T)` of the zeros of zeta with ordinate in `(0, T]`, the zero at height `T` counted
with half weight, the midpoint convention for `S (T)`. On the far range `10 ^ 13 ≤ T` the input
is Corollary 1 of Trudgian, JNT 134 (2014):
`|N (T) - T / (2π) log (T / (2π e)) - 7/8| ≤ 0.112 log T + 0.278 log log T + 2.510 + 0.2 / T`
for `T ≥ e`. That is the one cited leaf, shared by the three files of this branch.

The rest is proved: the level one bridge, the evaluation of `bookMain` and `bookError` at
`q = 1`, and the arithmetic
`7/8 + 0.112 log T + 0.278 log log T + 2.510 + 0.2 / T ≤ 0.15 log T + 3.389` for `10 ^ 13 ≤ T`,
which reduces to `0.278 log L + 0.2 / T ≤ 0.038 L + 0.004` with `L = log T ≥ 27`, closed by the
tangent bound `log L ≤ log 29 + L / 29 - 1` and `log 29 ≤ 5 log 2`. The same inequality fails
near `T = 10 ^ 6` and holds from about `T = 10 ^ 10` on; this range starts at `10 ^ 13`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF: explicit Riemann von Mangoldt formula for zeta, in the lab count. HARD, CITED:
Trudgian, J. Number Theory 134 (2014), Corollary 1, page 2, deduced there from Theorem 1 by
display (2.5): for `T ≥ e`, `|N (T) - T / (2π) log (T / (2π e)) - 7/8|` is at most
`0.112 log T + 0.278 log log T + 2.510 + 0.2 / T`. `N (T)` is `bookCount` of the trivial
character modulo one, whose `L`-function is `riemannZeta`; the half weight at `T` is the
midpoint convention for `S (T)`. -/
theorem trudgian2014_corollary1_far_cited (T : ℝ) (hTe : Real.exp 1 ≤ T) :
    |bookCount (1 : DirichletCharacter ℂ 1) T
        - T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) - 7 / 8|
      ≤ 0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.510 + 0.2 / T := by
  sorry

/-- Level one bridge: every Dirichlet character of modulus one is the trivial character
modulo one (`DirichletCharacter.level_one`), so the lab count is the count for that
character. -/
theorem far_level_one_bookCount (χ : DirichletCharacter ℂ q) (hq1 : q = 1) (T : ℝ) :
    bookCount χ T = bookCount (1 : DirichletCharacter ℂ 1) T := by
  subst hq1
  rw [DirichletCharacter.level_one χ]

/-- The book main term at `q = 1`. -/
theorem far_bookMain_one (hq1 : q = 1) (T : ℝ) :
    bookMain q T = T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) := by
  subst hq1
  simp [bookMain]

/-- The book error term at `q = 1`. -/
theorem far_bookError_one (hq1 : q = 1) (T : ℝ) :
    bookError q T = 0.15 * Real.log T + 3.389 := by
  subst hq1
  simp [bookError]

/-- `log T ≥ 27` for `T ≥ 10 ^ 13`, from `log 10 ≥ log 8 = 3 log 2`. -/
theorem far_log_ge_27 {T : ℝ} (hT13 : 10 ^ 13 ≤ T) : 27 ≤ Real.log T := by
  have h2 := Real.log_two_gt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h10 : Real.log 8 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
  have h13 : Real.log ((10 : ℝ) ^ 13) = 13 * Real.log 10 := by
    rw [Real.log_pow]; norm_num
  have hmono : Real.log ((10 : ℝ) ^ 13) ≤ Real.log T :=
    Real.log_le_log (by norm_num) hT13
  linarith

/-- The log log term against the slack: `0.278 log x ≤ 0.038 x - 0.001` for `x ≥ 27`. -/
theorem far_loglog_arith {x : ℝ} (hx : 27 ≤ x) :
    0.278 * Real.log x ≤ 0.038 * x - 0.001 := by
  have hxpos : 0 < x := by linarith
  have htan : Real.log (x / 29) ≤ x / 29 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hxpos.ne' (by norm_num)] at htan
  have h29 : Real.log 29 ≤ 5 * Real.log 2 := by
    have : Real.log (2 ^ 5 : ℝ) = 5 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]; exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9
  nlinarith

/-- Arithmetic of the far range:
`7/8 + 0.112 log T + 0.278 log log T + 2.510 + 0.2 / T ≤ 0.15 log T + 3.389` for `10 ^ 13 ≤ T`. -/
theorem far_budget_arith {T : ℝ} (hT13 : 10 ^ 13 ≤ T) :
    7 / 8 + (0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.510 + 0.2 / T)
      ≤ 0.15 * Real.log T + 3.389 := by
  have hL := far_log_ge_27 hT13
  have hll := far_loglog_arith hL
  have hinv : 0.2 / T ≤ 0.2 / 10 ^ 13 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT13
  norm_num at hinv hll ⊢
  linarith

/-- The common assembly for the far range: from the cited leaf, for `q = 1` and `10 ^ 13 ≤ T`,
the upper side of the book count. -/
theorem far_upper_from_cited (χ : DirichletCharacter ℂ q) {T : ℝ} (hq1 : q = 1)
    (hT13 : 10 ^ 13 ≤ T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  have he : Real.exp 1 ≤ T := by
    have := Real.exp_one_lt_d9
    linarith
  have h := trudgian2014_corollary1_far_cited T he
  rw [far_level_one_bookCount χ hq1, far_bookMain_one hq1, far_bookError_one hq1]
  have h1 := (abs_le.mp h).2
  have h2 := far_budget_arith hT13
  linarith

/-- Exact statement of `book_zero_count_large_height_upper_tall_level_one_far_scale_low_far`,
proved from the cited leaf `trudgian2014_corollary1_far_cited` and the proved bridge and
arithmetic. -/
theorem book_zero_count_large_height_upper_tall_level_one_far_scale_low_far_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT13 : 10 ^ 13 ≤ T) (hT20 : T ≤ 10 ^ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T :=
  far_upper_from_cited χ hq1 hT13

end LeanLab.HelfgottMajor.ZeroCount1623

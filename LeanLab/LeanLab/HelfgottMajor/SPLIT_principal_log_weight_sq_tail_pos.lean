import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long

/-!
Splitting the positive tail energy `principal_log_weight_sq_tail_pos`, the square energy of the
logarithmic derivative weight on `5 < t` bounded by twenty.

The tail is cut once more, at height eight.  On the near piece `5 < t ≤ 8` the interval is short
and only the size of the weight is paid for; on the far piece `8 < t` only the decay is paid for.
Both pieces are compared against the same elementary majorant `(2 log t + 3) ^ 2 / t ^ 2`, whose
primitive `-((2 log t) ^ 2 + 20 log t + 29) / t` gives the two numerical values `3.322` and
`10.988`, and the two budgets four and sixteen add up to twenty.

Every leaf below is one step of that comparison: the pointwise square bound, integrability of the
majorant on each piece, and the two numerical integrals.  The partition identity, the monotone
comparison on each piece and the final addition are proved here, leaving no gap.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457
open Complex
open Filter
open scoped Topology
open LeanLab.HelfgottMajor.Decomp457b.DigammaBudget


/-! ### The `Re s = 3 / 2` head: the von Mangoldt sum below one hundred -/

/-- `x ^ (3/2) = x * √x` on the nonnegative axis. -/
private theorem rpow_three_halves (x : ℝ) (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- `Λ 2 / 2^{3/2} ≤ 0.24509`. -/
private theorem head_2 :
    ArithmeticFunction.vonMangoldt 2 / (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.24509 := by
  have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 2 ≤ 0.6932 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 12, (0.6932 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 0.6932 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 2 (by norm_num)]
  have hs : (1.4142 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 4 / 4^{3/2} ≤ 0.08665`. -/
private theorem head_4 :
    ArithmeticFunction.vonMangoldt 4 / (4 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.08665 := by
  have hΛ : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 2 ≤ 0.6932 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 12, (0.6932 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 0.6932 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 4 (by norm_num)]
  have hs : (2.0000 : ℝ) ≤ Real.sqrt 4 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 4 * Real.sqrt 4 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 8 / 8^{3/2} ≤ 0.03064`. -/
private theorem head_8 :
    ArithmeticFunction.vonMangoldt 8 / (8 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.03064 := by
  have hΛ : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 2 ≤ 0.6932 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 12, (0.6932 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 0.6932 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 8 (by norm_num)]
  have hs : (2.8284 : ℝ) ≤ Real.sqrt 8 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 8 * Real.sqrt 8 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 16 / 16^{3/2} ≤ 0.01084`. -/
private theorem head_16 :
    ArithmeticFunction.vonMangoldt 16 / (16 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.01084 := by
  have hΛ : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 2 ≤ 0.6932 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 12, (0.6932 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 0.6932 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 16 (by norm_num)]
  have hs : (4.0000 : ℝ) ≤ Real.sqrt 16 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 16 * Real.sqrt 16 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 32 / 32^{3/2} ≤ 0.00383`. -/
private theorem head_32 :
    ArithmeticFunction.vonMangoldt 32 / (32 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00383 := by
  have hΛ : ArithmeticFunction.vonMangoldt 32 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 2 ≤ 0.6932 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 12, (0.6932 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 0.6932 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 32 (by norm_num)]
  have hs : (5.6568 : ℝ) ≤ Real.sqrt 32 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 32 * Real.sqrt 32 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 64 / 64^{3/2} ≤ 0.00136`. -/
private theorem head_64 :
    ArithmeticFunction.vonMangoldt 64 / (64 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00136 := by
  have hΛ : ArithmeticFunction.vonMangoldt 64 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 2 ≤ 0.6932 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 12, (0.6932 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 0.6932 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 64 (by norm_num)]
  have hs : (8.0000 : ℝ) ≤ Real.sqrt 64 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 64 * Real.sqrt 64 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 3 / 3^{3/2} ≤ 0.21146`. -/
private theorem head_3 :
    ArithmeticFunction.vonMangoldt 3 / (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.21146 := by
  have hΛ : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 3 ≤ 1.0987 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (3 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.0987 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.0987 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 3 (by norm_num)]
  have hs : (1.7320 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 3 * Real.sqrt 3 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 9 / 9^{3/2} ≤ 0.0407`. -/
private theorem head_9 :
    ArithmeticFunction.vonMangoldt 9 / (9 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.0407 := by
  have hΛ : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 3 ≤ 1.0987 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (3 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.0987 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.0987 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 9 (by norm_num)]
  have hs : (3.0000 : ℝ) ≤ Real.sqrt 9 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 9 * Real.sqrt 9 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 27 / 27^{3/2} ≤ 0.00784`. -/
private theorem head_27 :
    ArithmeticFunction.vonMangoldt 27 / (27 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00784 := by
  have hΛ : ArithmeticFunction.vonMangoldt 27 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 3 ≤ 1.0987 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (3 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.0987 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.0987 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 27 (by norm_num)]
  have hs : (5.1961 : ℝ) ≤ Real.sqrt 27 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 27 * Real.sqrt 27 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 81 / 81^{3/2} ≤ 0.00151`. -/
private theorem head_81 :
    ArithmeticFunction.vonMangoldt 81 / (81 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00151 := by
  have hΛ : ArithmeticFunction.vonMangoldt 81 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 3 ≤ 1.0987 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (3 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.0987 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.0987 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 81 (by norm_num)]
  have hs : (9.0000 : ℝ) ≤ Real.sqrt 81 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 81 * Real.sqrt 81 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 5 / 5^{3/2} ≤ 0.14397`. -/
private theorem head_5 :
    ArithmeticFunction.vonMangoldt 5 / (5 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.14397 := by
  have hΛ : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 5 ≤ 1.6095 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.6095 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.6095 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 5 (by norm_num)]
  have hs : (2.2360 : ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 5 * Real.sqrt 5 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 25 / 25^{3/2} ≤ 0.01288`. -/
private theorem head_25 :
    ArithmeticFunction.vonMangoldt 25 / (25 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.01288 := by
  have hΛ : ArithmeticFunction.vonMangoldt 25 = Real.log 5 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 5 ≤ 1.6095 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.6095 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.6095 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 25 (by norm_num)]
  have hs : (5.0000 : ℝ) ≤ Real.sqrt 25 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 25 * Real.sqrt 25 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 7 / 7^{3/2} ≤ 0.10508`. -/
private theorem head_7 :
    ArithmeticFunction.vonMangoldt 7 / (7 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.10508 := by
  have hΛ : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 7 ≤ 1.9460 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (7 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.9460 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.9460 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 7 (by norm_num)]
  have hs : (2.6457 : ℝ) ≤ Real.sqrt 7 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 7 * Real.sqrt 7 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 49 / 49^{3/2} ≤ 0.00568`. -/
private theorem head_49 :
    ArithmeticFunction.vonMangoldt 49 / (49 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00568 := by
  have hΛ : ArithmeticFunction.vonMangoldt 49 = Real.log 7 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 7 ≤ 1.9460 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (7 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.9460 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1.9460 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 49 (by norm_num)]
  have hs : (7.0000 : ℝ) ≤ Real.sqrt 49 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 49 * Real.sqrt 49 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 11 / 11^{3/2} ≤ 0.06812`. -/
private theorem head_11 :
    ArithmeticFunction.vonMangoldt 11 / (11 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.06812 := by
  have hΛ : ArithmeticFunction.vonMangoldt 11 = Real.log 11 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 11 ≤ 2.4851 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (11 : ℝ) ≤ ∑ i ∈ Finset.range 12, (2.4851 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 2.4851 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 11 (by norm_num)]
  have hs : (3.3166 : ℝ) ≤ Real.sqrt 11 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 11 * Real.sqrt 11 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 13 / 13^{3/2} ≤ 0.05631`. -/
private theorem head_13 :
    ArithmeticFunction.vonMangoldt 13 / (13 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.05631 := by
  have hΛ : ArithmeticFunction.vonMangoldt 13 = Real.log 13 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 13 ≤ 2.6392 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (13 : ℝ) ≤ ∑ i ∈ Finset.range 12, (2.6392 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 2.6392 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 13 (by norm_num)]
  have hs : (3.6055 : ℝ) ≤ Real.sqrt 13 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 13 * Real.sqrt 13 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 17 / 17^{3/2} ≤ 0.04124`. -/
private theorem head_17 :
    ArithmeticFunction.vonMangoldt 17 / (17 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.04124 := by
  have hΛ : ArithmeticFunction.vonMangoldt 17 = Real.log 17 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 17 ≤ 2.8906 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (17 : ℝ) ≤ ∑ i ∈ Finset.range 12, (2.8906 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 2.8906 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 17 (by norm_num)]
  have hs : (4.1231 : ℝ) ≤ Real.sqrt 17 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 17 * Real.sqrt 17 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 19 / 19^{3/2} ≤ 0.03618`. -/
private theorem head_19 :
    ArithmeticFunction.vonMangoldt 19 / (19 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.03618 := by
  have hΛ : ArithmeticFunction.vonMangoldt 19 = Real.log 19 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 19 ≤ 2.9959 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (19 : ℝ) ≤ ∑ i ∈ Finset.range 12, (2.9959 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 2.9959 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 19 (by norm_num)]
  have hs : (4.3588 : ℝ) ≤ Real.sqrt 19 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 19 * Real.sqrt 19 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 23 / 23^{3/2} ≤ 0.02882`. -/
private theorem head_23 :
    ArithmeticFunction.vonMangoldt 23 / (23 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.02882 := by
  have hΛ : ArithmeticFunction.vonMangoldt 23 = Real.log 23 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 23 ≤ 3.1783 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (23 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.1783 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 3.1783 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 23 (by norm_num)]
  have hs : (4.7958 : ℝ) ≤ Real.sqrt 23 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 23 * Real.sqrt 23 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 29 / 29^{3/2} ≤ 0.02179`. -/
private theorem head_29 :
    ArithmeticFunction.vonMangoldt 29 / (29 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.02179 := by
  have hΛ : ArithmeticFunction.vonMangoldt 29 = Real.log 29 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 29 ≤ 3.4014 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (29 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.4014 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 3.4014 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 29 (by norm_num)]
  have hs : (5.3851 : ℝ) ≤ Real.sqrt 29 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 29 * Real.sqrt 29 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 31 / 31^{3/2} ≤ 0.02009`. -/
private theorem head_31 :
    ArithmeticFunction.vonMangoldt 31 / (31 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.02009 := by
  have hΛ : ArithmeticFunction.vonMangoldt 31 = Real.log 31 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 31 ≤ 3.4660 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (31 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.4660 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 3.4660 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 31 (by norm_num)]
  have hs : (5.5677 : ℝ) ≤ Real.sqrt 31 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 31 * Real.sqrt 31 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 37 / 37^{3/2} ≤ 0.0164`. -/
private theorem head_37 :
    ArithmeticFunction.vonMangoldt 37 / (37 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.0164 := by
  have hΛ : ArithmeticFunction.vonMangoldt 37 = Real.log 37 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 37 ≤ 3.6891 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (37 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.6891 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 3.6891 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 37 (by norm_num)]
  have hs : (6.0827 : ℝ) ≤ Real.sqrt 37 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 37 * Real.sqrt 37 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 41 / 41^{3/2} ≤ 0.01424`. -/
private theorem head_41 :
    ArithmeticFunction.vonMangoldt 41 / (41 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.01424 := by
  have hΛ : ArithmeticFunction.vonMangoldt 41 = Real.log 41 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 41 ≤ 3.7379 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (41 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.7379 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 3.7379 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 41 (by norm_num)]
  have hs : (6.4031 : ℝ) ≤ Real.sqrt 41 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 41 * Real.sqrt 41 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 43 / 43^{3/2} ≤ 0.01351`. -/
private theorem head_43 :
    ArithmeticFunction.vonMangoldt 43 / (43 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.01351 := by
  have hΛ : ArithmeticFunction.vonMangoldt 43 = Real.log 43 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 43 ≤ 3.8069 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (43 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.8069 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 3.8069 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 43 (by norm_num)]
  have hs : (6.5574 : ℝ) ≤ Real.sqrt 43 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 43 * Real.sqrt 43 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 47 / 47^{3/2} ≤ 0.01202`. -/
private theorem head_47 :
    ArithmeticFunction.vonMangoldt 47 / (47 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.01202 := by
  have hΛ : ArithmeticFunction.vonMangoldt 47 = Real.log 47 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 47 ≤ 3.8715 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (47 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.8715 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 3.8715 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 47 (by norm_num)]
  have hs : (6.8556 : ℝ) ≤ Real.sqrt 47 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 47 * Real.sqrt 47 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 53 / 53^{3/2} ≤ 0.01034`. -/
private theorem head_53 :
    ArithmeticFunction.vonMangoldt 53 / (53 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.01034 := by
  have hΛ : ArithmeticFunction.vonMangoldt 53 = Real.log 53 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 53 ≤ 3.9893 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (53 : ℝ) ≤ ∑ i ∈ Finset.range 12, (3.9893 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 3.9893 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 53 (by norm_num)]
  have hs : (7.2801 : ℝ) ≤ Real.sqrt 53 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 53 * Real.sqrt 53 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 59 / 59^{3/2} ≤ 0.00904`. -/
private theorem head_59 :
    ArithmeticFunction.vonMangoldt 59 / (59 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00904 := by
  have hΛ : ArithmeticFunction.vonMangoldt 59 = Real.log 59 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 59 ≤ 4.0946 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (59 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.0946 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.0946 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 59 (by norm_num)]
  have hs : (7.6811 : ℝ) ≤ Real.sqrt 59 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 59 * Real.sqrt 59 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 61 / 61^{3/2} ≤ 0.0087`. -/
private theorem head_61 :
    ArithmeticFunction.vonMangoldt 61 / (61 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.0087 := by
  have hΛ : ArithmeticFunction.vonMangoldt 61 = Real.log 61 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 61 ≤ 4.1434 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (61 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.1434 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.1434 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 61 (by norm_num)]
  have hs : (7.8102 : ℝ) ≤ Real.sqrt 61 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 61 * Real.sqrt 61 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 67 / 67^{3/2} ≤ 0.00775`. -/
private theorem head_67 :
    ArithmeticFunction.vonMangoldt 67 / (67 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00775 := by
  have hΛ : ArithmeticFunction.vonMangoldt 67 = Real.log 67 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 67 ≤ 4.2487 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (67 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.2487 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.2487 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 67 (by norm_num)]
  have hs : (8.1853 : ℝ) ≤ Real.sqrt 67 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 67 * Real.sqrt 67 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 71 / 71^{3/2} ≤ 0.00715`. -/
private theorem head_71 :
    ArithmeticFunction.vonMangoldt 71 / (71 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00715 := by
  have hΛ : ArithmeticFunction.vonMangoldt 71 = Real.log 71 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 71 ≤ 4.2770 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (71 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.2770 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.2770 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 71 (by norm_num)]
  have hs : (8.4261 : ℝ) ≤ Real.sqrt 71 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 71 * Real.sqrt 71 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 73 / 73^{3/2} ≤ 0.00693`. -/
private theorem head_73 :
    ArithmeticFunction.vonMangoldt 73 / (73 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00693 := by
  have hΛ : ArithmeticFunction.vonMangoldt 73 = Real.log 73 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 73 ≤ 4.3177 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (73 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.3177 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.3177 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 73 (by norm_num)]
  have hs : (8.5440 : ℝ) ≤ Real.sqrt 73 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 73 * Real.sqrt 73 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 79 / 79^{3/2} ≤ 0.00625`. -/
private theorem head_79 :
    ArithmeticFunction.vonMangoldt 79 / (79 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00625 := by
  have hΛ : ArithmeticFunction.vonMangoldt 79 = Real.log 79 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 79 ≤ 4.3823 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (79 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.3823 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.3823 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 79 (by norm_num)]
  have hs : (8.8881 : ℝ) ≤ Real.sqrt 79 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 79 * Real.sqrt 79 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 83 / 83^{3/2} ≤ 0.00586`. -/
private theorem head_83 :
    ArithmeticFunction.vonMangoldt 83 / (83 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00586 := by
  have hΛ : ArithmeticFunction.vonMangoldt 83 = Real.log 83 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 83 ≤ 4.4311 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (83 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.4311 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.4311 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 83 (by norm_num)]
  have hs : (9.1104 : ℝ) ≤ Real.sqrt 83 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 83 * Real.sqrt 83 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 89 / 89^{3/2} ≤ 0.00536`. -/
private theorem head_89 :
    ArithmeticFunction.vonMangoldt 89 / (89 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.00536 := by
  have hΛ : ArithmeticFunction.vonMangoldt 89 = Real.log 89 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 89 ≤ 4.5001 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (89 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.5001 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.5001 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 89 (by norm_num)]
  have hs : (9.4339 : ℝ) ≤ Real.sqrt 89 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 89 * Real.sqrt 89 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `Λ 97 / 97^{3/2} ≤ 0.0048`. -/
private theorem head_97 :
    ArithmeticFunction.vonMangoldt 97 / (97 : ℝ) ^ (3 / 2 : ℝ) ≤ 0.0048 := by
  have hΛ : ArithmeticFunction.vonMangoldt 97 = Real.log 97 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  have hlp : Real.log 97 ≤ 4.5852 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (97 : ℝ) ≤ ∑ i ∈ Finset.range 12, (4.5852 : ℝ) ^ i / (i.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 4.5852 := Real.sum_le_exp_of_nonneg (by norm_num) _
  rw [hΛ, rpow_three_halves 97 (by norm_num)]
  have hs : (9.8488 : ℝ) ≤ Real.sqrt 97 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : (0 : ℝ) < 97 * Real.sqrt 97 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith

/-- `0.6931 ≤ Λ 2`. -/
private theorem low_2 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 2 := by
  have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (2 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (2 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 4`. -/
private theorem low_4 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 4 := by
  have hΛ : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (2 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (2 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 8`. -/
private theorem low_8 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 8 := by
  have hΛ : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (2 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (2 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 16`. -/
private theorem low_16 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 16 := by
  have hΛ : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (2 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (2 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 32`. -/
private theorem low_32 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 32 := by
  have hΛ : ArithmeticFunction.vonMangoldt 32 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (2 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (2 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 64`. -/
private theorem low_64 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 64 := by
  have hΛ : ArithmeticFunction.vonMangoldt 64 = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (2 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (2 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 3`. -/
private theorem low_3 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 3 := by
  have hΛ : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (3 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (3 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 9`. -/
private theorem low_9 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 9 := by
  have hΛ : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (3 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (3 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 27`. -/
private theorem low_27 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 27 := by
  have hΛ : ArithmeticFunction.vonMangoldt 27 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (3 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (3 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `0.6931 ≤ Λ 81`. -/
private theorem low_81 : (0.6931 : ℝ) ≤ ArithmeticFunction.vonMangoldt 81 := by
  have hΛ : ArithmeticFunction.vonMangoldt 81 = Real.log 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 1 : ℕ) : ℝ) ≤ (3 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 1 : ℕ)) : ℝ) ≤ Real.log (3 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 1 : ℕ)) : ℝ) = 1 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `1.3862 ≤ Λ 5`. -/
private theorem low_5 : (1.3862 : ℝ) ≤ ArithmeticFunction.vonMangoldt 5 := by
  have hΛ : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 2 : ℕ) : ℝ) ≤ (5 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 2 : ℕ)) : ℝ) ≤ Real.log (5 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 2 : ℕ)) : ℝ) = 2 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `1.3862 ≤ Λ 25`. -/
private theorem low_25 : (1.3862 : ℝ) ≤ ArithmeticFunction.vonMangoldt 25 := by
  have hΛ : ArithmeticFunction.vonMangoldt 25 = Real.log 5 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 2 : ℕ) : ℝ) ≤ (5 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 2 : ℕ)) : ℝ) ≤ Real.log (5 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 2 : ℕ)) : ℝ) = 2 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `1.3862 ≤ Λ 7`. -/
private theorem low_7 : (1.3862 : ℝ) ≤ ArithmeticFunction.vonMangoldt 7 := by
  have hΛ : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 2 : ℕ) : ℝ) ≤ (7 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 2 : ℕ)) : ℝ) ≤ Real.log (7 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 2 : ℕ)) : ℝ) = 2 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `1.3862 ≤ Λ 49`. -/
private theorem low_49 : (1.3862 : ℝ) ≤ ArithmeticFunction.vonMangoldt 49 := by
  have hΛ : ArithmeticFunction.vonMangoldt 49 = Real.log 7 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 2 : ℕ) : ℝ) ≤ (7 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 2 : ℕ)) : ℝ) ≤ Real.log (7 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 2 : ℕ)) : ℝ) = 2 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `2.0793 ≤ Λ 11`. -/
private theorem low_11 : (2.0793 : ℝ) ≤ ArithmeticFunction.vonMangoldt 11 := by
  have hΛ : ArithmeticFunction.vonMangoldt 11 = Real.log 11 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 3 : ℕ) : ℝ) ≤ (11 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 3 : ℕ)) : ℝ) ≤ Real.log (11 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 3 : ℕ)) : ℝ) = 3 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `2.0793 ≤ Λ 13`. -/
private theorem low_13 : (2.0793 : ℝ) ≤ ArithmeticFunction.vonMangoldt 13 := by
  have hΛ : ArithmeticFunction.vonMangoldt 13 = Real.log 13 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 3 : ℕ) : ℝ) ≤ (13 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 3 : ℕ)) : ℝ) ≤ Real.log (13 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 3 : ℕ)) : ℝ) = 3 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `2.7724 ≤ Λ 17`. -/
private theorem low_17 : (2.7724 : ℝ) ≤ ArithmeticFunction.vonMangoldt 17 := by
  have hΛ : ArithmeticFunction.vonMangoldt 17 = Real.log 17 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 4 : ℕ) : ℝ) ≤ (17 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 4 : ℕ)) : ℝ) ≤ Real.log (17 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 4 : ℕ)) : ℝ) = 4 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `2.7724 ≤ Λ 19`. -/
private theorem low_19 : (2.7724 : ℝ) ≤ ArithmeticFunction.vonMangoldt 19 := by
  have hΛ : ArithmeticFunction.vonMangoldt 19 = Real.log 19 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 4 : ℕ) : ℝ) ≤ (19 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 4 : ℕ)) : ℝ) ≤ Real.log (19 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 4 : ℕ)) : ℝ) = 4 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `2.7724 ≤ Λ 23`. -/
private theorem low_23 : (2.7724 : ℝ) ≤ ArithmeticFunction.vonMangoldt 23 := by
  have hΛ : ArithmeticFunction.vonMangoldt 23 = Real.log 23 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 4 : ℕ) : ℝ) ≤ (23 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 4 : ℕ)) : ℝ) ≤ Real.log (23 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 4 : ℕ)) : ℝ) = 4 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `2.7724 ≤ Λ 29`. -/
private theorem low_29 : (2.7724 : ℝ) ≤ ArithmeticFunction.vonMangoldt 29 := by
  have hΛ : ArithmeticFunction.vonMangoldt 29 = Real.log 29 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 4 : ℕ) : ℝ) ≤ (29 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 4 : ℕ)) : ℝ) ≤ Real.log (29 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 4 : ℕ)) : ℝ) = 4 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `2.7724 ≤ Λ 31`. -/
private theorem low_31 : (2.7724 : ℝ) ≤ ArithmeticFunction.vonMangoldt 31 := by
  have hΛ : ArithmeticFunction.vonMangoldt 31 = Real.log 31 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 4 : ℕ) : ℝ) ≤ (31 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 4 : ℕ)) : ℝ) ≤ Real.log (31 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 4 : ℕ)) : ℝ) = 4 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `3.4655 ≤ Λ 37`. -/
private theorem low_37 : (3.4655 : ℝ) ≤ ArithmeticFunction.vonMangoldt 37 := by
  have hΛ : ArithmeticFunction.vonMangoldt 37 = Real.log 37 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 5 : ℕ) : ℝ) ≤ (37 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 5 : ℕ)) : ℝ) ≤ Real.log (37 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 5 : ℕ)) : ℝ) = 5 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `3.4655 ≤ Λ 41`. -/
private theorem low_41 : (3.4655 : ℝ) ≤ ArithmeticFunction.vonMangoldt 41 := by
  have hΛ : ArithmeticFunction.vonMangoldt 41 = Real.log 41 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 5 : ℕ) : ℝ) ≤ (41 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 5 : ℕ)) : ℝ) ≤ Real.log (41 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 5 : ℕ)) : ℝ) = 5 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `3.4655 ≤ Λ 43`. -/
private theorem low_43 : (3.4655 : ℝ) ≤ ArithmeticFunction.vonMangoldt 43 := by
  have hΛ : ArithmeticFunction.vonMangoldt 43 = Real.log 43 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 5 : ℕ) : ℝ) ≤ (43 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 5 : ℕ)) : ℝ) ≤ Real.log (43 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 5 : ℕ)) : ℝ) = 5 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `3.4655 ≤ Λ 47`. -/
private theorem low_47 : (3.4655 : ℝ) ≤ ArithmeticFunction.vonMangoldt 47 := by
  have hΛ : ArithmeticFunction.vonMangoldt 47 = Real.log 47 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 5 : ℕ) : ℝ) ≤ (47 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 5 : ℕ)) : ℝ) ≤ Real.log (47 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 5 : ℕ)) : ℝ) = 5 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `3.4655 ≤ Λ 53`. -/
private theorem low_53 : (3.4655 : ℝ) ≤ ArithmeticFunction.vonMangoldt 53 := by
  have hΛ : ArithmeticFunction.vonMangoldt 53 = Real.log 53 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 5 : ℕ) : ℝ) ≤ (53 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 5 : ℕ)) : ℝ) ≤ Real.log (53 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 5 : ℕ)) : ℝ) = 5 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `3.4655 ≤ Λ 59`. -/
private theorem low_59 : (3.4655 : ℝ) ≤ ArithmeticFunction.vonMangoldt 59 := by
  have hΛ : ArithmeticFunction.vonMangoldt 59 = Real.log 59 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 5 : ℕ) : ℝ) ≤ (59 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 5 : ℕ)) : ℝ) ≤ Real.log (59 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 5 : ℕ)) : ℝ) = 5 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `3.4655 ≤ Λ 61`. -/
private theorem low_61 : (3.4655 : ℝ) ≤ ArithmeticFunction.vonMangoldt 61 := by
  have hΛ : ArithmeticFunction.vonMangoldt 61 = Real.log 61 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 5 : ℕ) : ℝ) ≤ (61 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 5 : ℕ)) : ℝ) ≤ Real.log (61 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 5 : ℕ)) : ℝ) = 5 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `4.1586 ≤ Λ 67`. -/
private theorem low_67 : (4.1586 : ℝ) ≤ ArithmeticFunction.vonMangoldt 67 := by
  have hΛ : ArithmeticFunction.vonMangoldt 67 = Real.log 67 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 6 : ℕ) : ℝ) ≤ (67 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 6 : ℕ)) : ℝ) ≤ Real.log (67 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 6 : ℕ)) : ℝ) = 6 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `4.1586 ≤ Λ 71`. -/
private theorem low_71 : (4.1586 : ℝ) ≤ ArithmeticFunction.vonMangoldt 71 := by
  have hΛ : ArithmeticFunction.vonMangoldt 71 = Real.log 71 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 6 : ℕ) : ℝ) ≤ (71 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 6 : ℕ)) : ℝ) ≤ Real.log (71 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 6 : ℕ)) : ℝ) = 6 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `4.1586 ≤ Λ 73`. -/
private theorem low_73 : (4.1586 : ℝ) ≤ ArithmeticFunction.vonMangoldt 73 := by
  have hΛ : ArithmeticFunction.vonMangoldt 73 = Real.log 73 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 6 : ℕ) : ℝ) ≤ (73 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 6 : ℕ)) : ℝ) ≤ Real.log (73 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 6 : ℕ)) : ℝ) = 6 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `4.1586 ≤ Λ 79`. -/
private theorem low_79 : (4.1586 : ℝ) ≤ ArithmeticFunction.vonMangoldt 79 := by
  have hΛ : ArithmeticFunction.vonMangoldt 79 = Real.log 79 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 6 : ℕ) : ℝ) ≤ (79 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 6 : ℕ)) : ℝ) ≤ Real.log (79 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 6 : ℕ)) : ℝ) = 6 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `4.1586 ≤ Λ 83`. -/
private theorem low_83 : (4.1586 : ℝ) ≤ ArithmeticFunction.vonMangoldt 83 := by
  have hΛ : ArithmeticFunction.vonMangoldt 83 = Real.log 83 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 6 : ℕ) : ℝ) ≤ (83 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 6 : ℕ)) : ℝ) ≤ Real.log (83 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 6 : ℕ)) : ℝ) = 6 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `4.1586 ≤ Λ 89`. -/
private theorem low_89 : (4.1586 : ℝ) ≤ ArithmeticFunction.vonMangoldt 89 := by
  have hΛ : ArithmeticFunction.vonMangoldt 89 = Real.log 89 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 6 : ℕ) : ℝ) ≤ (89 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 6 : ℕ)) : ℝ) ≤ Real.log (89 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 6 : ℕ)) : ℝ) = 6 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

/-- `4.1586 ≤ Λ 97`. -/
private theorem low_97 : (4.1586 : ℝ) ≤ ArithmeticFunction.vonMangoldt 97 := by
  have hΛ : ArithmeticFunction.vonMangoldt 97 = Real.log 97 := by
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
    norm_num
  rw [hΛ]
  have hle : ((2 ^ 6 : ℕ) : ℝ) ≤ (97 : ℝ) := by norm_num
  have h1 : Real.log (((2 ^ 6 : ℕ)) : ℝ) ≤ Real.log (97 : ℝ) :=
    Real.log_le_log (by norm_num) hle
  have h2 : Real.log (((2 ^ 6 : ℕ)) : ℝ) = 6 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  linarith

set_option maxHeartbeats 2000000 in
/-- `Λ n = 0` off the prime powers below one hundred, checked case by case. -/
private theorem vonMangoldt_zero_off_pp :
    ∀ n ∈ Finset.range 100, n ∉ ({2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64, 67, 71, 73, 79, 81, 83, 89, 97} : Finset ℕ) → ArithmeticFunction.vonMangoldt n = 0 := by
  intro n hn hmem
  have hlt : n < 100 := Finset.mem_range.mp hn
  interval_cases n
  all_goals first
    | (exfalso; revert hmem; decide)
    | rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (by decide +kernel)]

/-- A sum over the prime powers below one hundred is the sum over the whole range. -/
private theorem sum_pp_eq_sum_range (f : ℕ → ℝ)
    (hf : ∀ n ∈ Finset.range 100, n ∉ ({2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64, 67, 71, 73, 79, 81, 83, 89, 97} : Finset ℕ) → f n = 0) :
    ∑ n ∈ ({2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64, 67, 71, 73, 79, 81, 83, 89, 97} : Finset ℕ), f n = ∑ n ∈ Finset.range 100, f n :=
  Finset.sum_subset (by
    intro x hx
    simp only [Finset.mem_range]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega) hf

/-- `Σ_{n < 100} Λ n / n^{3/2} ≤ 1.30843`. -/
private theorem vonMangoldt_head100 :
    ∑ n ∈ Finset.range 100, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 1.30843 := by
  rw [← sum_pp_eq_sum_range (fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ))
    (fun n hn hmem => by rw [vonMangoldt_zero_off_pp n hn hmem, zero_div])]
  simp [Finset.sum_insert]
  linarith [head_2, head_4, head_8, head_16, head_32, head_64, head_3, head_9, head_27, head_81, head_5, head_25, head_7, head_49, head_11, head_13, head_17, head_19, head_23, head_29, head_31, head_37, head_41, head_43, head_47, head_53, head_59, head_61, head_67, head_71, head_73, head_79, head_83, head_89, head_97]

/-- `ψ 99 ≥ 83.865`: every prime power below one hundred contributes at least `log 2` per
power of two it contains. -/
private theorem psi99_ge : (83.865 : ℝ) ≤ Chebyshev.psi (99 : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc]
  norm_num
  rw [show (Finset.Icc 0 99 : Finset ℕ) = Finset.range 100 by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega]
  rw [← sum_pp_eq_sum_range (fun n => ArithmeticFunction.vonMangoldt n)
    (fun n hn hmem => vonMangoldt_zero_off_pp n hn hmem)]
  simp [Finset.sum_insert]
  linarith [low_2, low_4, low_8, low_16, low_32, low_64, low_3, low_9, low_27, low_81, low_5, low_25, low_7, low_49, low_11, low_13, low_17, low_19, low_23, low_29, low_31, low_37, low_41, low_43, low_47, low_53, low_59, low_61, low_67, low_71, low_73, low_79, low_83, low_89, low_97]


/-! ### The comparison function for the tail -/

/-- `log 4 ≤ 1.3863`. -/
private theorem dlog4 : Real.log 4 ≤ 1.3863 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_lt_d9
  rw [h]
  linarith

/-- `ψ x ≤ 1.3863 x + 2 √x log x` for `x ≥ 1`. -/
private theorem psi_envelope (x : ℝ) (hx : 1 ≤ x) :
    Chebyshev.psi x ≤ 1.3863 * x + 2 * Real.sqrt x * Real.log x := by
  have h := Chebyshev.psi_le hx
  have h4 := dlog4
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hm := mul_le_mul_of_nonneg_right h4 hx0
  linarith

/-- Derivative of `log x · x^{-2}`. -/
private theorem hasDerivAt_log_mul_inv_sq (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log t * t ^ (-(2 : ℝ)))
      (x ^ (-(3 : ℝ)) * (1 - 2 * Real.log x)) x := by
  have hL : HasDerivAt (fun t : ℝ => Real.log t) x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hP : HasDerivAt (fun t : ℝ => t ^ (-(2 : ℝ)))
      ((-(2 : ℝ)) * x ^ ((-(2 : ℝ)) - 1)) x :=
    Real.hasDerivAt_rpow_const (p := (-(2 : ℝ))) (Or.inl hx.ne')
  have h := hL.mul hP
  have e1 : ((-(2 : ℝ)) - 1) = -(3 : ℝ) := by norm_num
  rw [e1] at h
  convert h using 1
  have hx1 : x⁻¹ * x ^ (-(2 : ℝ)) = x ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
    norm_num
  rw [hx1]
  ring

/-- Derivative of the comparison function. -/
private theorem hasDerivAt_tailG (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => 2.0795 * t ^ (-(3 / 2) : ℝ) + 3 * (Real.log t * t ^ (-(2 : ℝ))))
      (2.0795 * ((-(3 / 2) : ℝ) * x ^ ((-(3 / 2) : ℝ) - 1))
        + 3 * (x ^ (-(3 : ℝ)) * (1 - 2 * Real.log x))) x := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ (-(3 / 2) : ℝ))
      ((-(3 / 2) : ℝ) * x ^ ((-(3 / 2) : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (p := (-(3 / 2) : ℝ)) (Or.inl hx.ne')
  have h2 : HasDerivAt (fun t : ℝ => 2.0795 * t ^ (-(3 / 2) : ℝ))
      (2.0795 * ((-(3 / 2) : ℝ) * x ^ ((-(3 / 2) : ℝ) - 1))) x := h1.const_mul 2.0795
  have h3 : HasDerivAt (fun t : ℝ => 3 * (Real.log t * t ^ (-(2 : ℝ))))
      (3 * (x ^ (-(3 : ℝ)) * (1 - 2 * Real.log x))) x :=
    (hasDerivAt_log_mul_inv_sq x hx).const_mul 3
  exact h2.add h3

/-- The comparison function `2.0795 t^{-3/2} + 3 log t t^{-2}` is antitone on `[99, ∞)`. -/
private theorem antitoneOn_tailG :
    AntitoneOn (fun t : ℝ => 2.0795 * t ^ (-(3 / 2) : ℝ) + 3 * (Real.log t * t ^ (-(2 : ℝ))))
      (Set.Ici 99) := by
  have hexp : Real.exp 1 ≤ (99 : ℝ) := by
    have h := Real.exp_one_lt_d9
    linarith
  have hlog99 : (1 : ℝ) ≤ Real.log 99 := (Real.le_log_iff_exp_le (by norm_num)).mpr hexp
  refine antitoneOn_of_deriv_nonpos (convex_Ici 99) ?_ ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.const_mul ?_ 2.0795
      exact ContinuousOn.rpow_const continuousOn_id
        (fun y hy => Or.inl (by have h := Set.mem_Ici.mp hy; linarith))
    · refine ContinuousOn.const_mul ?_ 3
      refine ContinuousOn.mul ?_ ?_
      · refine Real.continuousOn_log.mono ?_
        intro y hy
        have h := Set.mem_Ici.mp hy
        have h1 : (0 : ℝ) < y := by linarith
        simpa using h1.ne'
      · exact ContinuousOn.rpow_const continuousOn_id
          (fun y hy => Or.inl (by have h := Set.mem_Ici.mp hy; linarith))
  · intro y hy
    have hy99 : (99 : ℝ) < y := by
      rw [interior_Ici] at hy
      exact hy
    exact ((hasDerivAt_tailG y (by linarith)).differentiableAt).differentiableWithinAt
  · intro y hy
    have hy99 : (99 : ℝ) < y := by
      rw [interior_Ici] at hy
      exact hy
    have hpos : (0 : ℝ) < y := by linarith
    have hlogy : (1 : ℝ) ≤ Real.log y :=
      le_trans hlog99 (Real.log_le_log (by norm_num) (le_of_lt hy99))
    rw [(hasDerivAt_tailG y hpos).deriv]
    have hp1 : (0 : ℝ) < y ^ ((-(3 / 2) : ℝ) - 1) := Real.rpow_pos_of_pos hpos _
    have hp2 : (0 : ℝ) < y ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hpos _
    have hneg : 1 - 2 * Real.log y ≤ 0 := by linarith
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (by norm_num : (2.0795 * (-(3 / 2) : ℝ)) ≤ 0)
      (le_of_lt hp1), mul_nonpos_of_nonneg_of_nonpos (le_of_lt hp2) hneg]

/-- Integrability of `log x · x^{-2}` on `(99, ∞)`. -/
private theorem integrableOn_log_mul_inv_sq :
    IntegrableOn (fun t : ℝ => Real.log t * t ^ (-(2 : ℝ))) (Set.Ioi 99) := by
  have hmaj : IntegrableOn (fun t : ℝ => 4 * t ^ (-(7 / 4) : ℝ)) (Set.Ioi 99) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(7 / 4) : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 99)).const_mul 4
  have hcont : ContinuousOn (fun t : ℝ => Real.log t * t ^ (-(2 : ℝ))) (Set.Ioi (99 : ℝ)) := by
    refine ContinuousOn.mul ?_ ?_
    · refine Real.continuousOn_log.mono ?_
      intro y hy
      have h := Set.mem_Ioi.mp hy
      have h1 : (0 : ℝ) < y := by linarith
      simpa using h1.ne'
    · exact ContinuousOn.rpow_const continuousOn_id
        (fun y hy => Or.inl (by have h := Set.mem_Ioi.mp hy; linarith))
  refine hmaj.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx99 : (99 : ℝ) < x := Set.mem_Ioi.mp hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hl : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div (le_of_lt hx0) (by norm_num : (0 : ℝ) < 1 / 4)
    have e : x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) := by ring
    rwa [e] at h
  have hlogpos : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hstep : Real.log x * x ^ (-(2 : ℝ)) ≤ (4 * x ^ (1 / 4 : ℝ)) * x ^ (-(2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hl (le_of_lt (Real.rpow_pos_of_pos hx0 _))
  have hcalc : (4 * x ^ (1 / 4 : ℝ)) * x ^ (-(2 : ℝ)) = 4 * x ^ (-(7 / 4) : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hx0]
    norm_num
  linarith [hstep, hcalc]

/-- Integrability of the comparison function on `(99, ∞)`. -/
private theorem integrableOn_tailG :
    IntegrableOn (fun t : ℝ => 2.0795 * t ^ (-(3 / 2) : ℝ) + 3 * (Real.log t * t ^ (-(2 : ℝ))))
      (Set.Ioi 99) :=
  ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 99)).const_mul 2.0795).add
    (integrableOn_log_mul_inv_sq.const_mul 3)

/-- The comparison function is nonnegative on `(99, ∞)`. -/
private theorem tailG_nonneg {t : ℝ} (ht : t ∈ Set.Ioi (99 : ℝ)) :
    0 ≤ 2.0795 * t ^ (-(3 / 2) : ℝ) + 3 * (Real.log t * t ^ (-(2 : ℝ))) := by
  have ht99 : (99 : ℝ) < t := Set.mem_Ioi.mp ht
  have h0 : (0 : ℝ) < t := by linarith
  have hl : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by linarith)
  have h1 : (0 : ℝ) ≤ t ^ (-(3 / 2) : ℝ) := le_of_lt (Real.rpow_pos_of_pos h0 _)
  have h2 : (0 : ℝ) ≤ t ^ (-(2 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos h0 _)
  have : (0 : ℝ) ≤ 3 * (Real.log t * t ^ (-(2 : ℝ))) := by positivity
  linarith [this, h1]

/-- `log 99 ≤ 4.5960`. -/
private theorem dlog99 : Real.log 99 ≤ 4.5960 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (99 : ℝ) ≤ ∑ i ∈ Finset.range 14, (4.5960 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 4.5960 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- The primitive `-(log x + 1)/x` of `log x · x^{-2}`. -/
private theorem hasDerivAt_log_primitive (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(Real.log y + 1) / y) (Real.log x * x ^ (-(2 : ℝ))) x := by
  have hL : HasDerivAt (fun y : ℝ => Real.log y + 1) x⁻¹ x :=
    (Real.hasDerivAt_log hx.ne').add_const 1
  have hfun : (fun y : ℝ => -(Real.log y + 1) / y)
      = -((fun y : ℝ => Real.log y + 1) / (id : ℝ → ℝ)) := by
    funext y
    simp only [Pi.div_apply, Pi.neg_apply, id]
    rw [neg_div]
  have h : HasDerivAt (-((fun y : ℝ => Real.log y + 1) / (id : ℝ → ℝ)))
      (-((x⁻¹ * id x - (Real.log x + 1) * 1) / id x ^ 2)) x :=
    (hL.div (hasDerivAt_id x) hx.ne').neg
  have hd1 : (-((x⁻¹ * id x - (Real.log x + 1) * 1) / id x ^ 2) : ℝ) = Real.log x / x ^ 2 := by
    simp only [id]
    field_simp
    ring
  have hd2 : Real.log x / x ^ 2 = Real.log x * x ^ (-(2 : ℝ)) := by
    rw [show (-(2 : ℝ)) = -(1 : ℝ) + -(1 : ℝ) by norm_num, Real.rpow_add hx,
      Real.rpow_neg_one, div_eq_mul_inv]
    field_simp
  have hderiv_eq : (-((x⁻¹ * id x - (Real.log x + 1) * 1) / id x ^ 2) : ℝ)
      = Real.log x * x ^ (-(2 : ℝ)) := hd1.trans hd2
  have hh : HasDerivAt (-((fun y : ℝ => Real.log y + 1) / (id : ℝ → ℝ)))
      (Real.log x * x ^ (-(2 : ℝ))) x := h.congr_deriv hderiv_eq
  rwa [← hfun] at hh

/-- `∫_{99}^{∞} log x · x^{-2} = (log 99 + 1)/99`. -/
private theorem integral_Ioi_99_log_mul_inv_sq :
    ∫ x in Set.Ioi (99 : ℝ), Real.log x * x ^ (-(2 : ℝ)) = (Real.log 99 + 1) / 99 := by
  have hderiv : ∀ x ∈ Set.Ici (99 : ℝ),
      HasDerivAt (fun y : ℝ => -(Real.log y + 1) / y) (Real.log x * x ^ (-(2 : ℝ))) x :=
    fun x hx => hasDerivAt_log_primitive x (by have h := Set.mem_Ici.mp hx; linarith)
  have htend : Tendsto (fun y : ℝ => -(Real.log y + 1) / y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
      simpa using (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
    have h2 : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hev : (fun y : ℝ => -(Real.log y + 1) / y) =ᶠ[atTop] fun y => -(Real.log y / y) - y⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      field_simp
      ring
    rw [Filter.tendsto_congr' hev]
    simpa using h1.neg.sub h2
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv integrableOn_log_mul_inv_sq htend
  rw [hval]
  field_simp
  ring

/-- `∫_{99}^{∞} G ≤ 0.588`. -/
private theorem integral_Ioi_99_tailG_le :
    ∫ x in Set.Ioi (99 : ℝ), (2.0795 * x ^ (-(3 / 2) : ℝ) + 3 * (Real.log x * x ^ (-(2 : ℝ))))
      ≤ 0.588 := by
  have h1 : IntegrableOn (fun x : ℝ => 2.0795 * x ^ (-(3 / 2) : ℝ)) (Set.Ioi 99) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 99)).const_mul 2.0795
  have h2 : IntegrableOn (fun x : ℝ => 3 * (Real.log x * x ^ (-(2 : ℝ)))) (Set.Ioi 99) :=
    integrableOn_log_mul_inv_sq.const_mul 3
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_Ioi_99_log_mul_inv_sq,
    integral_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1) (by norm_num : (0 : ℝ) < 99)]
  have hsqrt : (99 : ℝ) ^ ((-(3 / 2) : ℝ) + 1) = (Real.sqrt 99)⁻¹ := by
    rw [show ((-(3 / 2) : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow]
  rw [hsqrt]
  have hden : ((-(3 / 2) : ℝ) + 1) = -(1 / 2) := by norm_num
  rw [hden]
  have hs : (9.9498 : ℝ) ≤ Real.sqrt 99 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hlog := dlog99
  have hpos : (0 : ℝ) < Real.sqrt 99 := Real.sqrt_pos.2 (by norm_num)
  have e : (-((Real.sqrt 99))⁻¹ / (-(1 / 2) : ℝ)) = 2 / Real.sqrt 99 := by
    have h2 : (0 : ℝ) < Real.sqrt 99 := Real.sqrt_pos.2 (by norm_num)
    field_simp
  rw [e]
  have e2 : 2 / Real.sqrt 99 ≤ 0.20101 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

/-! ### The von Mangoldt series below one and nine tenths -/

/-- `log n / n^{3/2}` is summable. -/
private theorem summable_log_div_rpow_32 :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 4) : ℝ)) := by
    have h := (Real.summable_nat_rpow_inv (p := (5 / 4 : ℝ))).mpr (by norm_num)
    exact h.congr (fun n => by rw [eq_comm, Real.rpow_neg (Nat.cast_nonneg n)])
  have hmaj : Summable (fun n : ℕ => 4 * (n : ℝ) ^ (-(5 / 4) : ℝ)) := hbase.mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      positivity
  · rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      have hlog : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
        have h1 := Real.log_le_rpow_div (le_of_lt hn) (by norm_num : (0 : ℝ) < 1 / 4)
        have h2 : (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by ring
        rwa [h2] at h1
      have h3 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ) := by
        rw [← Real.rpow_add hn]
        norm_num
      rw [h3]
      have hp1 : (0 : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hn _
      have hp2 : (0 : ℝ) < (n : ℝ) ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos hn _
      have h5 : 4 * (n : ℝ) ^ (1 / 4 : ℝ) / ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ))
          = 4 * (n : ℝ) ^ (-(5 / 4) : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hn)]
        field_simp
      calc Real.log (n : ℝ) / ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ))
          ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) / ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ)) :=
            div_le_div_of_nonneg_right hlog (le_of_lt (mul_pos hp1 hp2))
        _ = 4 * (n : ℝ) ^ (-(5 / 4) : ℝ) := h5

/-- The von Mangoldt series `Λ n / n^{3/2}` is summable. -/
private theorem summable_vonMangoldt_div_rpow_32 :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_log_div_rpow_32
  · positivity
  · exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)

/-- The same series, written with a reciprocal power. -/
private theorem summable_vonMangoldt_mul_rpow :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(3 / 2) : ℝ)) := by
  refine summable_vonMangoldt_div_rpow_32.congr (fun n => ?_)
  rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- `ψ` at a natural number is the von Mangoldt sum up to it. -/
private theorem psi_range_eq (M : ℕ) :
    (∑ j ∈ Finset.range (M + 1), (ArithmeticFunction.vonMangoldt j : ℝ)) = Chebyshev.psi (M : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  congr 1
  ext x
  simp only [Finset.mem_Icc, Finset.mem_range]
  omega

/-- The step `t^{-3/2}` drops by at most `(3/2) t^{-5/2}` per unit step. -/
private theorem rpow_diff_le (i : ℕ) (hi : 1 ≤ i) :
    (i : ℝ) ^ (-(3 / 2) : ℝ) - (((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
      ≤ (3 / 2) * (i : ℝ) ^ (-(5 / 2) : ℝ) := by
  have ha : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hlt : (i : ℝ) < (((i + 1 : ℕ)) : ℝ) := by push_cast; linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(3 / 2) : ℝ)) (Set.Icc (i : ℝ) (((i + 1 : ℕ)) : ℝ)) := by
    refine ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl ?_)
    have h1 : (0 : ℝ) < t := lt_of_lt_of_le ha (Set.mem_Icc.mp ht).1
    exact h1.ne'
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ (-(3 / 2) : ℝ))
      (Set.Ioo (i : ℝ) (((i + 1 : ℕ)) : ℝ)) := by
    intro t ht
    have h1 : (0 : ℝ) < t := lt_trans ha ht.1
    exact (Real.hasDerivAt_rpow_const (p := (-(3 / 2) : ℝ)) (Or.inl h1.ne')).differentiableAt
      |>.differentiableWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope (f := fun t : ℝ => t ^ (-(3 / 2) : ℝ))
    hlt hcont hdiff
  have hc0 : (0 : ℝ) < c := lt_trans ha hc.1
  have hderiv : deriv (fun t : ℝ => t ^ (-(3 / 2) : ℝ)) c
      = (-(3 / 2) : ℝ) * c ^ ((-(3 / 2) : ℝ) - 1) :=
    (Real.hasDerivAt_rpow_const (p := (-(3 / 2) : ℝ)) (Or.inl hc0.ne')).deriv
  have hcb : (((i + 1 : ℕ)) : ℝ) - (i : ℝ) = 1 := by push_cast; ring
  rw [hderiv, hcb, div_one] at hslope
  -- hslope : -(3/2) * c ^ (-(5/2)) = f (i+1) - f i
  have hci : (i : ℝ) ≤ c := le_of_lt hc.1
  have hmono : c ^ ((-(3 / 2) : ℝ) - 1) ≤ (i : ℝ) ^ ((-(3 / 2) : ℝ) - 1) := by
    have he : ((-(3 / 2) : ℝ) - 1) = -(5 / 2 : ℝ) := by norm_num
    rw [he]
    exact Real.rpow_le_rpow_of_nonpos ha hci (by norm_num)
  rw [show ((-(3 / 2) : ℝ) - 1) = -(5 / 2 : ℝ) by norm_num] at hslope hmono
  linarith [mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 3 / 2)]

/-- Abel summation for the von Mangoldt series from `100` to `M`. -/
private theorem vonMangoldt_abel (M : ℕ) (hM : 100 ≤ M) :
    (∑ i ∈ Finset.Ico 100 (M + 1), (i : ℝ) ^ (-(3 / 2) : ℝ) * (ArithmeticFunction.vonMangoldt i : ℝ))
      = (M : ℝ) ^ (-(3 / 2) : ℝ) * (∑ j ∈ Finset.range (M + 1), (ArithmeticFunction.vonMangoldt j : ℝ))
        - (100 : ℝ) ^ (-(3 / 2) : ℝ) * (∑ j ∈ Finset.range 100, (ArithmeticFunction.vonMangoldt j : ℝ))
        - ∑ i ∈ Finset.Ico 100 M,

            ((((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) - (i : ℝ) ^ (-(3 / 2) : ℝ))
              * (∑ j ∈ Finset.range (i + 1), (ArithmeticFunction.vonMangoldt j : ℝ)) := by
  have h := Finset.sum_Ico_by_parts (f := fun i : ℕ => (i : ℝ) ^ (-(3 / 2) : ℝ))
    (g := fun i : ℕ => (ArithmeticFunction.vonMangoldt i : ℝ)) (m := 100) (n := M + 1)
    (by omega)
  simpa [smul_eq_mul, Nat.add_sub_cancel] using h

/-- The tail of the von Mangoldt series beyond one hundred. -/
private theorem vonMangoldt_tail_le :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt (n + 100) : ℝ)
      * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)) ≤ 0.588 - 0.083865 := by
  have hsum : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 100) : ℝ)
      * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (summable_nat_add_iff 100).mpr summable_vonMangoldt_mul_rpow
  have hsG0 : Summable (fun n : ℕ =>
      2.0795 * (n : ℝ) ^ (-(3 / 2) : ℝ) + 3 * (Real.log (n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)))) :=
    antitoneOn_tailG.summable_of_integrableOn_Ioi integrableOn_tailG (fun t ht => tailG_nonneg ht)
  have hsG : Summable (fun n : ℕ => 2.0795 * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
      + 3 * (Real.log (((n + 100 : ℕ)) : ℝ) * (((n + 100 : ℕ)) : ℝ) ^ (-(2 : ℝ)))) :=
    (summable_nat_add_iff 100).mpr hsG0
  have hpoint : ∀ i : ℕ, 100 ≤ i →
      ((i : ℝ) ^ (-(3 / 2) : ℝ) - (((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ))
        * (∑ j ∈ Finset.range (i + 1), (ArithmeticFunction.vonMangoldt j : ℝ))
      ≤ 2.0795 * (i : ℝ) ^ (-(3 / 2) : ℝ) + 3 * (Real.log (i : ℝ) * (i : ℝ) ^ (-(2 : ℝ))) := by
    intro i hi
    have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
    have hd := rpow_diff_le i (by omega : 1 ≤ i)
    have hmono : (((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) ≤ (i : ℝ) ^ (-(3 / 2) : ℝ) := by
      refine Real.rpow_le_rpow_of_nonpos hi0 ?_ (by norm_num)
      push_cast
      linarith
    have hd0 : (0 : ℝ) ≤ (i : ℝ) ^ (-(3 / 2) : ℝ) - (((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) := by
      linarith
    have hpsi : (∑ j ∈ Finset.range (i + 1), (ArithmeticFunction.vonMangoldt j : ℝ))
        ≤ 1.3863 * (i : ℝ) + 2 * Real.sqrt (i : ℝ) * Real.log (i : ℝ) := by
      rw [psi_range_eq i]
      exact psi_envelope (i : ℝ) (by exact_mod_cast (by omega : 1 ≤ i))
    have hpsi0 : (0 : ℝ) ≤ (∑ j ∈ Finset.range (i + 1), (ArithmeticFunction.vonMangoldt j : ℝ)) :=
      Finset.sum_nonneg (fun j _ => ArithmeticFunction.vonMangoldt_nonneg)
    have henv : (0 : ℝ) ≤ 1.3863 * (i : ℝ) + 2 * Real.sqrt (i : ℝ) * Real.log (i : ℝ) := by
      have hl : (0 : ℝ) ≤ Real.log (i : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ i))
      nlinarith [Real.sqrt_nonneg (i : ℝ)]
    have hb0 : (0 : ℝ) ≤ (3 / 2) * (i : ℝ) ^ (-(5 / 2) : ℝ) := by
      have := Real.rpow_pos_of_pos hi0 (-(5 / 2) : ℝ)
      linarith
    refine (mul_le_mul hd hpsi hpsi0 hb0).trans ?_
    have e1 : (i : ℝ) ^ (-(5 / 2) : ℝ) * (i : ℝ) = (i : ℝ) ^ (-(3 / 2) : ℝ) := by
      nth_rewrite 2 [← Real.rpow_one (i : ℝ)]
      rw [← Real.rpow_add hi0]
      norm_num
    have e2 : (i : ℝ) ^ (-(5 / 2) : ℝ) * (i : ℝ) ^ (1 / 2 : ℝ) = (i : ℝ) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hi0]
      norm_num
    have e3 : (i : ℝ) ^ (-(5 / 2) : ℝ) * Real.sqrt (i : ℝ) = (i : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, e2]
    calc (3 / 2) * (i : ℝ) ^ (-(5 / 2) : ℝ)
          * (1.3863 * (i : ℝ) + 2 * Real.sqrt (i : ℝ) * Real.log (i : ℝ))
        = (3 / 2 * 1.3863) * ((i : ℝ) ^ (-(5 / 2) : ℝ) * (i : ℝ))
          + (3 * ((i : ℝ) ^ (-(5 / 2) : ℝ) * Real.sqrt (i : ℝ))) * Real.log (i : ℝ) := by ring
      _ = (3 / 2 * 1.3863) * (i : ℝ) ^ (-(3 / 2) : ℝ)
          + 3 * (Real.log (i : ℝ) * (i : ℝ) ^ (-(2 : ℝ))) := by
          rw [e1, e3]
          ring
      _ ≤ 2.0795 * (i : ℝ) ^ (-(3 / 2) : ℝ) + 3 * (Real.log (i : ℝ) * (i : ℝ) ^ (-(2 : ℝ))) := by
          have hp1 : (0 : ℝ) ≤ (i : ℝ) ^ (-(3 / 2) : ℝ) := le_of_lt (Real.rpow_pos_of_pos hi0 _)
          nlinarith
  have hpart : ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt (n + 100) : ℝ)
        * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ))
      ≤ (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
          * (1.3863 * (((99 + N : ℕ)) : ℝ) + 2 * Real.sqrt (((99 + N : ℕ)) : ℝ)
              * Real.log (((99 + N : ℕ)) : ℝ))
        - 0.083865 + 0.588 := by
    intro N hN1
    have hM100 : 100 ≤ 99 + N := by
      have h := Nat.add_le_add_left hN1 99
      simpa using h
    have hab := vonMangoldt_abel (99 + N) hM100
    have hre : (∑ i ∈ Finset.Ico 100 (99 + N + 1),
          (i : ℝ) ^ (-(3 / 2) : ℝ) * (ArithmeticFunction.vonMangoldt i : ℝ))
        = (∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt (n + 100) : ℝ)
            * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)) := by
      rw [Finset.sum_Ico_eq_sum_range (f := fun i : ℕ =>
        (i : ℝ) ^ (-(3 / 2) : ℝ) * (ArithmeticFunction.vonMangoldt i : ℝ))]
      · have hN : 99 + N + 1 - 100 = N := by
          have h : 99 + N + 1 = N + 100 := by ring
          rw [h, Nat.add_sub_cancel]
        rw [hN]
        apply Finset.sum_congr rfl
        intro n _
        rw [Nat.add_comm 100 n, mul_comm]
    have hG99 : (83.865 : ℝ) ≤ (∑ j ∈ Finset.range 100, (ArithmeticFunction.vonMangoldt j : ℝ)) := by
      rw [psi_range_eq 99]
      exact psi99_ge
    have hGM : (∑ j ∈ Finset.range (99 + N + 1), (ArithmeticFunction.vonMangoldt j : ℝ))
        ≤ 1.3863 * (((99 + N : ℕ)) : ℝ) + 2 * Real.sqrt (((99 + N : ℕ)) : ℝ)
            * Real.log (((99 + N : ℕ)) : ℝ) := by
      rw [psi_range_eq (99 + N)]
      exact psi_envelope (((99 + N : ℕ)) : ℝ) (by exact_mod_cast (by omega : 1 ≤ 99 + N))
    have hS : -(∑ i ∈ Finset.Ico 100 (99 + N),
          ((((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) - (i : ℝ) ^ (-(3 / 2) : ℝ))
            * (∑ j ∈ Finset.range (i + 1), (ArithmeticFunction.vonMangoldt j : ℝ))) ≤ 0.588 := by
      have hneg : -(∑ i ∈ Finset.Ico 100 (99 + N),
            ((((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) - (i : ℝ) ^ (-(3 / 2) : ℝ))
              * (∑ j ∈ Finset.range (i + 1), (ArithmeticFunction.vonMangoldt j : ℝ)))
          = ∑ i ∈ Finset.Ico 100 (99 + N),
            (((i : ℝ) ^ (-(3 / 2) : ℝ) - (((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ))
              * (∑ j ∈ Finset.range (i + 1), (ArithmeticFunction.vonMangoldt j : ℝ))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hneg]
      calc (∑ i ∈ Finset.Ico 100 (99 + N),
            (((i : ℝ) ^ (-(3 / 2) : ℝ) - (((i + 1 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ))
              * (∑ j ∈ Finset.range (i + 1), (ArithmeticFunction.vonMangoldt j : ℝ))))
          ≤ ∑ i ∈ Finset.Ico 100 (99 + N),
              (2.0795 * (i : ℝ) ^ (-(3 / 2) : ℝ) + 3 * (Real.log (i : ℝ) * (i : ℝ) ^ (-(2 : ℝ)))) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            rw [Finset.mem_Ico] at hi
            exact hpoint i hi.1
        _ = ∑ n ∈ Finset.range (99 + N - 100),
               (2.0795 * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
                 + 3 * (Real.log (((n + 100 : ℕ)) : ℝ) * (((n + 100 : ℕ)) : ℝ) ^ (-(2 : ℝ)))) := by
            rw [Finset.sum_Ico_eq_sum_range (f := fun i : ℕ =>
              2.0795 * (i : ℝ) ^ (-(3 / 2) : ℝ) + 3 * (Real.log (i : ℝ) * (i : ℝ) ^ (-(2 : ℝ))))]
            apply Finset.sum_congr rfl
            intro k _
            rw [Nat.add_comm 100 k]
        _ ≤ ∑' n : ℕ, (2.0795 * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
               + 3 * (Real.log (((n + 100 : ℕ)) : ℝ) * (((n + 100 : ℕ)) : ℝ) ^ (-(2 : ℝ)))) := by
            refine Summable.sum_le_tsum _ (fun n => ?_) hsG
            have h0 : (0 : ℝ) < (((n + 100 : ℕ)) : ℝ) := by positivity
            have hl : (0 : ℝ) ≤ Real.log (((n + 100 : ℕ)) : ℝ) := Real.log_nonneg (by push_cast; linarith)
            have h1 : (0 : ℝ) ≤ (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) :=
              le_of_lt (Real.rpow_pos_of_pos h0 _)
            have h2 : (0 : ℝ) ≤ (((n + 100 : ℕ)) : ℝ) ^ (-(2 : ℝ)) :=
              le_of_lt (Real.rpow_pos_of_pos h0 _)
            have h3 : (0 : ℝ) ≤ 3 * (Real.log (((n + 100 : ℕ)) : ℝ)
                * (((n + 100 : ℕ)) : ℝ) ^ (-(2 : ℝ))) := by
              have := mul_nonneg hl h2
              linarith
            have h4 : (0 : ℝ) ≤ 2.0795 * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) := by linarith
            exact fun _ => add_nonneg h4 h3
        _ ≤ ∫ x in Set.Ioi (99 : ℝ),
              (2.0795 * x ^ (-(3 / 2) : ℝ) + 3 * (Real.log x * x ^ (-(2 : ℝ)))) :=
            (by
              have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ =>
                2.0795 * x ^ (-(3 / 2) : ℝ) + 3 * (Real.log x * x ^ (-(2 : ℝ))))
                (N := 99) antitoneOn_tailG integrableOn_tailG (fun t ht => tailG_nonneg ht)
              have hidx : (fun n : ℕ => (fun x : ℝ => 2.0795 * x ^ (-(3 / 2) : ℝ)
                    + 3 * (Real.log x * x ^ (-(2 : ℝ)))) (((n + 99 + 1 : ℕ)) : ℝ))
                  = fun n : ℕ => 2.0795 * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
                    + 3 * (Real.log (((n + 100 : ℕ)) : ℝ) * (((n + 100 : ℕ)) : ℝ) ^ (-(2 : ℝ))) := by
                funext n
                have h1 : n + 99 + 1 = n + 100 := by ring
                rw [h1]
              rw [hidx] at h
              exact h)
        _ ≤ 0.588 := integral_Ioi_99_tailG_le
    have hMNpos : (0 : ℝ) < ((99 + N : ℕ) : ℝ) := by positivity
    have hA := mul_le_mul_of_nonneg_left hGM
      (le_of_lt (Real.rpow_pos_of_pos hMNpos (-(3 / 2 : ℝ))))
    have hB := mul_le_mul_of_nonneg_left hG99
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 100) (-(3 / 2 : ℝ))))
    have hf100 : (100 : ℝ) ^ (-(3 / 2) : ℝ) = 1 / 1000 := by
      rw [Real.rpow_neg (by norm_num),
        show (100 : ℝ) ^ (3 / 2 : ℝ) = 1000 by
          rw [show (3 / 2 : ℝ) = 1 / 2 * 3 by norm_num, Real.rpow_mul (by norm_num),
            show (100 : ℝ) ^ (1 / 2 : ℝ) = 10 by
              rw [← Real.sqrt_eq_rpow, show (100 : ℝ) = 10 ^ 2 by norm_num,
                Real.sqrt_sq (by norm_num)]]
          norm_num]
      norm_num
    have hB' : (100 : ℝ) ^ (-(3 / 2) : ℝ)
        * (∑ j ∈ Finset.range 100, (ArithmeticFunction.vonMangoldt j : ℝ)) ≥ 0.083865 := by
      rw [hf100]
      linarith [hG99]
    rw [← hre, hab]
    linarith [hA, hB', hS]
  have htend : Tendsto (fun N : ℕ => (((99 + N : ℕ)) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => (((N + 99 : ℕ)) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 99)
    simpa [Nat.add_comm] using h1
  have hhalf : Tendsto (fun N : ℕ => (((99 + N : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp htend
  have hlogdiv : Tendsto (fun N : ℕ => Real.log (((99 + N : ℕ)) : ℝ) / (((99 + N : ℕ)) : ℝ))
      atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero).comp htend
    simpa [Function.comp_def, Real.rpow_one] using h
  have hprod : Tendsto (fun N : ℕ => (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
      * (1.3863 * (((99 + N : ℕ)) : ℝ) + 2 * Real.sqrt (((99 + N : ℕ)) : ℝ)
        * Real.log (((99 + N : ℕ)) : ℝ))) atTop (𝓝 0) := by
    have heq : ∀ N : ℕ, (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
        * (1.3863 * (((99 + N : ℕ)) : ℝ) + 2 * Real.sqrt (((99 + N : ℕ)) : ℝ)
          * Real.log (((99 + N : ℕ)) : ℝ))
        = 1.3863 * (((99 + N : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ)
          + 2 * (Real.log (((99 + N : ℕ)) : ℝ) / (((99 + N : ℕ)) : ℝ)) := by
      intro N
      have h0 : (0 : ℝ) < (((99 + N : ℕ)) : ℝ) := by positivity
      have e1 : (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) * (((99 + N : ℕ)) : ℝ)
          = (((99 + N : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ) := by
        have h2 : (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) * (((99 + N : ℕ)) : ℝ) ^ (1 : ℝ)
            = (((99 + N : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ) := by
          rw [← Real.rpow_add h0]
          norm_num
        rwa [Real.rpow_one] at h2
      have e3 : (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) * Real.sqrt (((99 + N : ℕ)) : ℝ)
          = (((99 + N : ℕ)) : ℝ)⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add h0]
        rw [show (-(3 / 2) : ℝ) + 1 / 2 = -(1 : ℝ) by norm_num, Real.rpow_neg_one]
      rw [mul_add]
      have h1' : (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) * (1.3863 * (((99 + N : ℕ)) : ℝ))
          = 1.3863 * (((99 + N : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ) := by
        calc (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) * (1.3863 * (((99 + N : ℕ)) : ℝ))
            = 1.3863 * ((((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) * (((99 + N : ℕ)) : ℝ)) := by ring
          _ = 1.3863 * (((99 + N : ℕ)) : ℝ) ^ (-(1 / 2) : ℝ) := by rw [e1]
      have h2' : (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
          * (2 * Real.sqrt (((99 + N : ℕ)) : ℝ) * Real.log (((99 + N : ℕ)) : ℝ))
          = 2 * (Real.log (((99 + N : ℕ)) : ℝ) / (((99 + N : ℕ)) : ℝ)) := by
        calc (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
              * (2 * Real.sqrt (((99 + N : ℕ)) : ℝ) * Real.log (((99 + N : ℕ)) : ℝ))
            = 2 * ((((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) * Real.sqrt (((99 + N : ℕ)) : ℝ))
              * Real.log (((99 + N : ℕ)) : ℝ) := by ring
          _ = 2 * (Real.log (((99 + N : ℕ)) : ℝ) / (((99 + N : ℕ)) : ℝ)) := by
              rw [e3, div_eq_mul_inv]
              ring
      rw [h1', h2']
    rw [Filter.tendsto_congr' (Filter.Eventually.of_forall heq)]
    have h := (hhalf.const_mul (1.3863 : ℝ)).add (hlogdiv.const_mul 2)
    simpa using h
  have hbound : Tendsto (fun N : ℕ => (((99 + N : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)
      * (1.3863 * (((99 + N : ℕ)) : ℝ) + 2 * Real.sqrt (((99 + N : ℕ)) : ℝ)
        * Real.log (((99 + N : ℕ)) : ℝ)) - 0.083865 + 0.588) atTop (𝓝 (0 - 0.083865 + 0.588)) :=
    (hprod.sub_const 0.083865).add_const 0.588
  obtain ⟨T, hT⟩ := hsum
  have hleft : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      (ArithmeticFunction.vonMangoldt (n + 100) : ℝ) * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ)))
      atTop (𝓝 T) := hT.tendsto_sum_nat
  have hle : T ≤ 0 - 0.083865 + 0.588 :=
    le_of_tendsto_of_tendsto hleft hbound
      (Filter.eventually_atTop.2 ⟨1, fun n hn => hpart n hn⟩)
  rw [hT.tsum_eq]
  linarith

/-- `Σ' n, Λ n / n^{3/2} ≤ 19/10`. -/
private theorem vonMangoldt_tsum_le :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ 19 / 10 := by
  rw [← summable_vonMangoldt_div_rpow_32.sum_add_tsum_nat_add 100]
  have htail : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt (n + 100) : ℝ)
      / (((n + 100 : ℕ)) : ℝ) ^ (3 / 2 : ℝ)) ≤ 0.588 - 0.083865 := by
    have heq : (fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 100) : ℝ)
        / (((n + 100 : ℕ)) : ℝ) ^ (3 / 2 : ℝ))
        = fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 100) : ℝ)
          * (((n + 100 : ℕ)) : ℝ) ^ (-(3 / 2) : ℝ) := by
      funext n
      rw [Real.rpow_neg (Nat.cast_nonneg (n + 100)), div_eq_mul_inv]
    rw [heq]
    exact vonMangoldt_tail_le
  linarith [vonMangoldt_head100, htail]

/-- LEAF. The zeta input. On the whole line of real part three halves the logarithmic
derivative of the Riemann zeta function is at most `19/10` in modulus. This is the first
input of the envelope: on that line the Dirichlet series for the logarithmic derivative is
dominated term by term by its value at the real point `3/2`, where the numeral is the one
the source prints. -/
private theorem zeta_three_half_bound (y : ℝ) :
    ‖logDeriv riemannZeta ((((3 / 2 : ℝ)) : ℂ) + y * Complex.I)‖ ≤ 19 / 10 := by
  set s : ℂ := (3 / 2 : ℂ) + y * Complex.I with hs
  have hkey : ‖logDeriv riemannZeta s‖ ≤ 19 / 10 := by
    have hre : 1 < s.re := by rw [hs]; simp; norm_num
    have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hre
    have he : logDeriv riemannZeta s
        = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
      rw [hL, logDeriv_apply]
      ring
    have hn : ∀ n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖
        = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) := by
      intro n
      rw [LSeries.norm_term_eq]
      split_ifs with hz
      · subst hz
        simp
      · rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        congr 1
        rw [hs]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero]
        norm_num
    have hsum_norm : Summable (fun n : ℕ =>
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖) :=
      summable_vonMangoldt_div_rpow_32.congr (fun n => (hn n).symm)
    rw [he, norm_neg]
    calc ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖
        ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
          norm_tsum_le_tsum_norm hsum_norm
      _ = ∑' n, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) := tsum_congr hn
      _ ≤ 19 / 10 := vonMangoldt_tsum_le
  have hfin : s = ((((3 / 2 : ℝ)) : ℂ) + y * Complex.I) := by
    rw [hs]
    push_cast
    ring
  rw [← hfin]
  exact hkey

private theorem half_line_mem_integerComplement (t : ℝ) :
    ((1 / 2 : ℂ) + t * I) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have he : (n : ℝ) = 1 / 2 := by
    have h := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.intCast_re, mul_zero, mul_one, sub_zero,
      add_zero] at h
    norm_num at h
    linarith
  have h2 : (2 : ℤ) * n = 1 := by
    have hh : (2 : ℝ) * (n : ℝ) = 1 := by rw [he]; norm_num
    exact_mod_cast hh
  omega

/-- The digamma recurrence, taken from `1/2 + it` up to `5/2 + it`. -/
private theorem digamma_half_shift (t : ℝ) :
    (Complex.digamma ((5 / 2 : ℂ) + t * I)).re =
      (Complex.digamma ((1 / 2 : ℂ) + t * I)).re
        + (((1 / 2 : ℂ) + t * I)⁻¹).re + (((3 / 2 : ℂ) + t * I)⁻¹).re := by
  have hs : ∀ m : ℕ, ((1 / 2 : ℂ) + t * I) ≠ -(m : ℂ) := by
    intro m hm
    exact half_line_mem_integerComplement t ⟨-(m : ℤ), by rw [hm]; push_cast; ring⟩
  have h1 := Complex.digamma_apply_add_one ((1 / 2 : ℂ) + t * I) hs
  have e1 : ((1 / 2 : ℂ) + t * I) + 1 = (3 / 2 : ℂ) + t * I := by push_cast; ring
  rw [e1] at h1
  have hs2 : ∀ m : ℕ, ((3 / 2 : ℂ) + t * I) ≠ -(m : ℂ) := by
    intro m hm
    have hh : (3 / 2 : ℝ) + (m : ℝ) = 0 := by
      have h := congrArg Complex.re hm
      simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.natCast_re, mul_zero, mul_one, sub_zero,
        add_zero, Complex.neg_re] at h
      norm_num at h
      linarith
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h2 := Complex.digamma_apply_add_one ((3 / 2 : ℂ) + t * I) hs2
  have e2 : ((3 / 2 : ℂ) + t * I) + 1 = (5 / 2 : ℂ) + t * I := by push_cast; ring
  rw [e2] at h2
  have r1 := congrArg Complex.re h1
  have r2 := congrArg Complex.re h2
  simp only [Complex.add_re] at r1 r2
  linarith

/-- Upper bound for the real part of `ψ(1/2 + it)`. -/
private theorem digamma_half_re_le (t : ℝ) (ht : 2 ≤ |t|) :
    (Complex.digamma ((1 / 2 : ℂ) + t * I)).re ≤ Real.log (|t| + 3) + 1 / 4 := by
  have h5 := digamma_re_le_five_half t
  have hs := digamma_half_shift t
  have hp1 : 0 ≤ (((1 / 2 : ℂ) + t * I)⁻¹).re := by
    have h := inv_re_vertical (1 / 2) t
    have e : (((1 / 2 : ℝ)) : ℂ) + t * I = (1 / 2 : ℂ) + t * I := by push_cast; ring
    rw [e] at h
    rw [h]
    positivity
  have hp2 : 0 ≤ (((3 / 2 : ℂ) + t * I)⁻¹).re := by
    have h := inv_re_vertical (3 / 2) t
    have e : (((3 / 2 : ℝ)) : ℂ) + t * I = (3 / 2 : ℂ) + t * I := by push_cast; ring
    rw [e] at h
    rw [h]
    positivity
  have harg : ‖(5 / 2 : ℂ) + t * I‖ ≤ |t| + 3 := by
    have hsq : ‖(5 / 2 : ℂ) + t * I‖ ^ 2 = (5 / 2 : ℝ) ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hle : (5 / 2 : ℝ) ^ 2 + t ^ 2 ≤ (|t| + 3) ^ 2 := by
      nlinarith [abs_nonneg t, sq_abs t]
    nlinarith [norm_nonneg ((5 / 2 : ℂ) + t * I)]
  have hpos : (0 : ℝ) < ‖(5 / 2 : ℂ) + t * I‖ := by
    have h := Complex.re_le_norm ((5 / 2 : ℂ) + t * I)
    have h2 : ((5 / 2 : ℂ) + t * I).re = 5 / 2 := by simp
    rw [h2] at h
    linarith
  have hlog : Real.log ‖(5 / 2 : ℂ) + t * I‖ ≤ Real.log (|t| + 3) :=
    Real.log_le_log hpos harg
  linarith

/-- Lower bound for the real part of `ψ(1/2 + it)`, from the sign of the terms of the
partial-fraction series: `1/(n+1) ≥ ℜ 1/(n + 3/2 + it)`. -/
private theorem digamma_half_re_ge (t : ℝ) (ht : 2 ≤ |t|) :
    -(5 / 4 : ℝ) ≤ (Complex.digamma ((1 / 2 : ℂ) + t * I)).re := by
  set z : ℂ := (1 / 2 : ℂ) + t * I with hz
  have hzc : z ∈ Complex.integerComplement := by
    rw [hz]; exact half_line_mem_integerComplement t
  have h := hasSum_digamma_series hzc
  have hterm : ∀ n : ℕ, 0 ≤ ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re := by
    intro n
    have hnorm : ((n : ℝ) + 3 / 2) ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 := Complex.re_le_norm (z + (n : ℂ) + 1)
      have h2 : (z + (n : ℂ) + 1).re = (n : ℝ) + 3 / 2 := by rw [hz]; simp; ring
      rw [h2] at h1
      linarith
    have hinv : |((1 / (z + n + 1) : ℂ)).re| ≤ 1 / ((n : ℝ) + 3 / 2) := by
      have h2 := Complex.abs_re_le_norm ((1 / (z + (n : ℂ) + 1) : ℂ))
      rw [norm_div, norm_one] at h2
      have hpos : (0 : ℝ) < (n : ℝ) + 3 / 2 := by positivity
      calc |((1 / (z + n + 1) : ℂ)).re| ≤ 1 / ‖z + (n : ℂ) + 1‖ := h2
        _ ≤ 1 / ((n : ℝ) + 3 / 2) := by
            apply one_div_le_one_div_of_le hpos hnorm
    have hA : ((1 / ((n : ℂ) + 1) : ℂ)).re = 1 / ((n : ℝ) + 1) := by
      have e : ((n : ℂ) + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) + (0 : ℝ) * I := by push_cast; ring
      rw [one_div, e, inv_re_vertical]
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [Complex.sub_re, hA]
    have h4 : (1 / (z + n + 1) : ℂ).re ≤ 1 / ((n : ℝ) + 3 / 2) := le_trans (le_abs_self _) hinv
    have h5 : 1 / ((n : ℝ) + 3 / 2) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  have hnonneg : 0 ≤ ∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re :=
    tsum_nonneg hterm
  have hL : (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z).re
      = ∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re := by
    rw [← h.tsum_eq]
    exact Complex.reCLM.map_tsum h.summable
  have hzre : (1 / z : ℂ).re ≤ 1 / 2 := by
    have h1 : (1 / z : ℂ).re ≤ ‖(1 / z : ℂ)‖ := Complex.re_le_norm _
    have h2 : ‖(1 / z : ℂ)‖ = 1 / ‖z‖ := by rw [norm_div, norm_one]
    have h3 : (2 : ℝ) ≤ ‖z‖ := by
      have hsq : ‖z‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
        rw [hz, Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      nlinarith [norm_nonneg z, abs_nonneg t, sq_abs t]
    have h4 : 1 / ‖z‖ ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) h3
    linarith
  have hγ : Real.eulerMascheroniConstant ≤ 2 / 3 := le_of_lt Real.eulerMascheroniConstant_lt_two_thirds
  have hEq : (Complex.digamma z).re
      = (∑' n : ℕ, ((1 / ((n : ℂ) + 1) - 1 / (z + n + 1) : ℂ)).re)
        - Real.eulerMascheroniConstant - (1 / z : ℂ).re := by
    rw [← hL]
    simp only [Complex.add_re, Complex.ofReal_re]
    ring
  rw [hEq]
  linarith

/-- Conjugacy of `ψ` on the line `Re s = 1/2`, from the partial-fraction series. -/
private theorem digamma_half_conj (t : ℝ) :
    Complex.digamma (star ((1 / 2 : ℂ) + t * I)) = star (Complex.digamma ((1 / 2 : ℂ) + t * I)) := by
  set z : ℂ := (1 / 2 : ℂ) + t * I with hz
  have hzc : z ∈ Complex.integerComplement := by rw [hz]; exact half_line_mem_integerComplement t
  have hzsc : star z ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    refine hzc ⟨n, ?_⟩
    have h := congrArg star hn
    simpa using h
  have h1 := hasSum_digamma_series hzsc
  have h2 := HasSum.star (hasSum_digamma_series hzc)
  have h2' : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (star z + (n : ℂ) + 1))
      (star (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)) := by
    convert h2 using 1
    ext n
    simp
  have huniq := h1.unique h2'
  have hs : star (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)
      = star (Complex.digamma z) + (Real.eulerMascheroniConstant : ℂ) + 1 / star z := by
    simp [star_div₀, star_add, star_one]
  rw [hs] at huniq
  exact add_right_cancel (add_right_cancel huniq)

/-- The imaginary part of `ψ(1/2 + it)` is `(π/2)·tanh(πt)`, hence at most `π/2` in modulus. -/
private theorem digamma_half_im_eq (t : ℝ) :
    (Complex.digamma ((1 / 2 : ℂ) + t * I)).im
      = Real.pi / 2 * Real.tanh (Real.pi * t) := by
  set z : ℂ := (1 / 2 : ℂ) + t * I with hz
  have hzint : ∀ n : ℤ, z ≠ n := by
    intro n hn
    exact half_line_mem_integerComplement t ⟨n, by rw [← hz]; exact hn.symm⟩
  have h1 := Complex.digamma_one_sub hzint
  have h1s : (1 : ℂ) - z = star z := by
    rw [hz]
    simp
    ring
  rw [h1s] at h1
  have hconj : Complex.digamma (star z) = star (Complex.digamma z) := by
    rw [hz]; exact digamma_half_conj t
  rw [hconj] at h1
  have hcos : Complex.cos (π * z) = -(↑(Real.sinh (π * t)) * I) := by
    have e : π * z = (((π / 2 : ℝ)) : ℂ) + ((π * t : ℝ)) * I := by rw [hz]; push_cast; ring
    rw [e, Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    ring
  have hsin : Complex.sin (π * z) = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    have e : π * z = (((π / 2 : ℝ)) : ℂ) + ((π * t : ℝ)) * I := by rw [hz]; push_cast; ring
    rw [e, Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    ring
  have hcot : Complex.cot (π * z)
      = (↑(-(Real.sinh (π * t) / Real.cosh (π * t))) : ℂ) * I := by
    rw [Complex.cot_eq_cos_div_sin, hcos, hsin]
    rw [show (-(↑(Real.sinh (π * t)) * I) : ℂ) = (↑(-(Real.sinh (π * t))) : ℂ) * I by
      push_cast; ring]
    rw [show ((↑(-(Real.sinh (π * t))) : ℂ) * I) / (↑(Real.cosh (π * t)) : ℂ)
        = ((↑(-(Real.sinh (π * t))) : ℂ) / ↑(Real.cosh (π * t))) * I by ring]
    rw [← Complex.ofReal_div]
    ring
  have hstar : (star (Complex.digamma z)).im = -(Complex.digamma z).im := by simp
  have him := congrArg Complex.im h1
  rw [hcot, hstar] at him
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_I_re, Complex.mul_I_im, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, zero_mul, add_zero, sub_zero, Complex.neg_re, Complex.neg_im] at him
  have htanh : Real.sinh (π * t) / Real.cosh (π * t) = Real.tanh (π * t) :=
    (Real.tanh_eq_sinh_div_cosh (π * t)).symm
  rw [hz] at him
  rw [htanh] at him
  have hX : (π : ℝ) * -(Real.tanh (π * t)) = -(π * Real.tanh (π * t)) := by ring
  rw [hX] at him
  have h2 : ((1 / 2 : ℂ) + (t : ℂ) * I).digamma.im = (π * Real.tanh (π * t)) / 2 := by
    linarith
  rw [h2]
  ring

private theorem tan_left_arg (t : ℝ) :
    π * ((-1 / 2 : ℂ) + t * Complex.I) / 2
      = ((-(π / 4) : ℝ) : ℂ) + ((π * t / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

private theorem tan_left_eq_of (y : ℝ) :
    Complex.tan ((-(π / 4) : ℝ) + y * Complex.I)
      = ((-1 : ℂ) + ((Real.tanh y : ℝ) : ℂ) * Complex.I) /
        (1 + ((Real.tanh y : ℝ) : ℂ) * Complex.I) := by
  have hx : ∀ k : ℤ, ((-(π / 4) : ℝ) : ℂ) ≠ (2 * (k : ℂ) + 1) * π / 2 := by
    intro k hk
    have hre : (-(π / 4) : ℝ) = (2 * (k : ℝ) + 1) * π / 2 := by
      simpa using congrArg Complex.re hk
    have hmul : (4 * (k : ℝ) + 3) * π = 0 := by linarith
    have hk3 : 4 * (k : ℝ) + 3 = 0 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact h
      · exact absurd h Real.pi_ne_zero
    have : (4 * k + 3 : ℤ) = 0 := by exact_mod_cast hk3
    omega
  have hy : ∀ l : ℤ, (y : ℂ) * Complex.I ≠ (2 * (l : ℂ) + 1) * π / 2 := by
    intro l hl
    have hre : (0 : ℝ) = (2 * (l : ℝ) + 1) * π / 2 := by
      simpa using congrArg Complex.re hl
    have hmul : (2 * (l : ℝ) + 1) * π = 0 := by linarith
    have hl0 : 2 * (l : ℝ) + 1 = 0 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact h
      · exact absurd h Real.pi_ne_zero
    have : (2 * l + 1 : ℤ) = 0 := by exact_mod_cast hl0
    omega
  rw [Complex.tan_add_mul_I (Or.inl ⟨hx, hy⟩)]
  have htx : Complex.tan ((-(π / 4) : ℝ) : ℂ) = -1 := by
    rw [← Complex.ofReal_tan, Real.tan_neg, Real.tan_pi_div_four]
    norm_num
  rw [htx, ← Complex.ofReal_tanh]
  congr 1
  ring

private theorem neg_one_add_mul_I_div (c : ℝ) :
    ((-1 : ℂ) + (c : ℂ) * Complex.I) / (1 + (c : ℂ) * Complex.I)
      = (((c ^ 2 - 1) / (1 + c ^ 2) : ℝ) : ℂ)
        + (((2 * c) / (1 + c ^ 2) : ℝ) : ℂ) * Complex.I := by
  have hden : (1 : ℂ) + (c : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, mul_zero, mul_one, add_zero, Complex.zero_re] at hre
    norm_num at hre
  apply Complex.ext
  · simp [Complex.div_re, Complex.div_im, Complex.normSq, ← Complex.ofReal_pow]
    field_simp
    ring
  · simp [Complex.div_re, Complex.div_im, Complex.normSq, ← Complex.ofReal_pow]
    field_simp
    ring

private theorem one_sub_tanh_sq (y : ℝ) :
    1 - Real.tanh y ^ 2 = 1 / Real.cosh y ^ 2 := by
  have hc : 0 < Real.cosh y := Real.cosh_pos y
  have hden : Real.cosh y ^ 2 ≠ 0 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq y]

private theorem cosh_sq_eq (y : ℝ) : Real.cosh y ^ 2 = 1 + Real.sinh y ^ 2 := by
  linarith [Real.cosh_sq_sub_sinh_sq y]

private theorem one_sub_tanh_sq_le (y : ℝ) (hy : 0 ≤ y) :
    1 - Real.tanh y ^ 2 ≤ 1 / (1 + y ^ 2) := by
  have hsinh : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy
  have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hcosh : 1 + y ^ 2 ≤ Real.cosh y ^ 2 := by
    rw [cosh_sq_eq]
    nlinarith [hsinh, hy]
  rw [one_sub_tanh_sq]
  have hc : 0 < Real.cosh y ^ 2 := by positivity
  exact one_div_le_one_div_of_le hpos hcosh

private theorem tanh_double (y : ℝ) :
    Real.tanh (y + y) = 2 * Real.tanh y / (1 + Real.tanh y ^ 2) := by
  have hpos : 0 < Real.cosh y := Real.cosh_pos y
  have hs : Real.sinh (y + y) = 2 * Real.sinh y * Real.cosh y := by
    rw [Real.sinh_add]; ring
  have hc : Real.cosh (y + y) = Real.cosh y ^ 2 + Real.sinh y ^ 2 := by
    rw [Real.cosh_add]; ring
  rw [Real.tanh_eq_sinh_div_cosh, hs, hc, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- The explicit form of the tangent factor. -/
private theorem tan_left_explicit (t : ℝ) :
    π / 2 * Complex.tan (π * ((-1 / 2 : ℂ) + t * Complex.I) / 2)
      = (((π / 2 * ((Real.tanh (π * t / 2) ^ 2 - 1) / (1 + Real.tanh (π * t / 2) ^ 2)) : ℝ)) : ℂ)
        + (((π / 2 * (2 * Real.tanh (π * t / 2) /
            (1 + Real.tanh (π * t / 2) ^ 2)) : ℝ)) : ℂ) * Complex.I := by
  rw [tan_left_arg t, tan_left_eq_of, neg_one_add_mul_I_div]
  push_cast
  ring

private theorem tan_left_im (t : ℝ) :
    (π / 2 * Complex.tan (π * ((-1 / 2 : ℂ) + t * Complex.I) / 2)).im
      = π / 2 * Real.tanh (π * t) := by
  rw [tan_left_explicit]
  have h2 : 2 * Real.tanh (π * t / 2) / (1 + Real.tanh (π * t / 2) ^ 2)
      = Real.tanh (π * t) := by
    have h3 := tanh_double (π * t / 2)
    rw [show π * t / 2 + π * t / 2 = π * t from by ring] at h3
    exact h3.symm
  rw [← h2]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_zero, mul_one, add_zero, zero_add]

private theorem tan_left_re_bounds (t : ℝ) (ht : 5 ≤ t) :
    -1 / 20 ≤ (π / 2 * Complex.tan (π * ((-1 / 2 : ℂ) + t * Complex.I) / 2)).re ∧
      (π / 2 * Complex.tan (π * ((-1 / 2 : ℂ) + t * Complex.I) / 2)).re ≤ 0 := by
  set c := Real.tanh (π * t / 2) with hc
  have hrew : π / 2 * Complex.tan (π * ((-1 / 2 : ℂ) + t * Complex.I) / 2)
      = (((π / 2 * ((c ^ 2 - 1) / (1 + c ^ 2)) : ℝ)) : ℂ)
        + (((π / 2 * (2 * c / (1 + c ^ 2)) : ℝ)) : ℂ) * Complex.I := by
    rw [tan_left_explicit, hc]
  have hre : (π / 2 * Complex.tan (π * ((-1 / 2 : ℂ) + t * Complex.I) / 2)).re
      = π / 2 * ((c ^ 2 - 1) / (1 + c ^ 2)) := by
    rw [hrew]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, add_zero, sub_zero, zero_mul]
  have hc1 : c ^ 2 ≤ 1 := by
    have h := Real.abs_tanh_lt_one (π * t / 2)
    rw [← hc] at h
    have h2 := abs_lt.mp h
    nlinarith [abs_nonneg c, sq_abs c, h2.1, h2.2]
  have hden : (0 : ℝ) < 1 + c ^ 2 := by positivity
  have hy : (0:ℝ) ≤ π * t / 2 := by positivity
  have hsmall : 1 - c ^ 2 ≤ 1 / 56 := by
    have h1 := one_sub_tanh_sq_le (π * t / 2) hy
    have h2 : (55 : ℝ) ≤ (π * t / 2) ^ 2 := by
      have hp := Real.pi_gt_three
      have hm : (3:ℝ) * 5 ≤ π * t := by
        exact mul_le_mul Real.pi_gt_three.le ht (by norm_num) Real.pi_pos.le
      have hpt : (7.5 : ℝ) ≤ π * t / 2 := by linarith
      have hpos : (0:ℝ) < π * t / 2 := by linarith
      nlinarith [hpt, sq_nonneg (π * t / 2 - 7.5)]
    have h4 : 1 / (1 + (π * t / 2) ^ 2) ≤ 1 / 56 := by
      apply one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  constructor
  · rw [hre]
    have h5 : -(π / 2) * ((1 - c ^ 2) / (1 + c ^ 2)) ≥ -(π / 2) * (1 / 56) := by
      have h6 : (1 - c ^ 2) / (1 + c ^ 2) ≤ 1 / 56 := by
        rw [div_le_div_iff₀ hden (by norm_num)]
        nlinarith [hsmall, hden]
      have hp : (0:ℝ) < π / 2 := by positivity
      have h7 := mul_le_mul_of_nonneg_left h6 hp.le
      linarith
    have he : π / 2 * ((c ^ 2 - 1) / (1 + c ^ 2)) = -(π / 2) * ((1 - c ^ 2) / (1 + c ^ 2)) := by
      field_simp
      ring
    rw [he]
    have hpi := Real.pi_lt_four
    nlinarith
  · rw [hre]
    have hp : (0:ℝ) < π / 2 := by positivity
    have hnn : 0 ≤ 1 - c ^ 2 := by nlinarith [hc1]
    have he : π / 2 * ((c ^ 2 - 1) / (1 + c ^ 2)) = -((π / 2) * ((1 - c ^ 2) / (1 + c ^ 2))) := by
      field_simp
      ring
    rw [he]
    have hpos : 0 ≤ (π / 2) * ((1 - c ^ 2) / (1 + c ^ 2)) := by positivity
    linarith


/-! ### The pointwise bound on the left line -/

/-- `-1/2 + i t` is not an integer. -/
private theorem left_point_mem_integerComplement (t : ℝ) :
    ((-1 / 2 : ℂ) + t * Complex.I) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have h := congrArg Complex.re hn
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero] at h
  norm_num at h
  have h2 : (2 : ℤ) * n = -1 := by
    have hh : (2 : ℝ) * (n : ℝ) = -1 := by linarith
    exact_mod_cast hh
  omega

/-- The reciprocal of `-1/2 + i t` has imaginary part `-t / (1/4 + t ^ 2)`. -/
private theorem inv_left_im (t : ℝ) :
    ((((-1 / 2 : ℂ) + t * Complex.I))⁻¹).im = -t / (1 / 4 + t ^ 2) := by
  have hns : Complex.normSq ((-1 / 2 : ℂ) + t * Complex.I) = 1 / 4 + t ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [Complex.inv_im, hns]
  simp

/-- The reciprocal of `-1/2 + i t` has real part `-(1/2) / (1/4 + t ^ 2)`. -/
private theorem inv_left_re (t : ℝ) :
    ((((-1 / 2 : ℂ) + t * Complex.I))⁻¹).re = -(1 / 2) / (1 / 4 + t ^ 2) := by
  have hns : Complex.normSq ((-1 / 2 : ℂ) + t * Complex.I) = 1 / 4 + t ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [Complex.inv_re, hns]
  simp
  ring

/-- The digamma recurrence from the left line to the half line. -/
private theorem digamma_left_shift (t : ℝ) :
    Complex.digamma ((1 / 2 : ℂ) + t * Complex.I)
      = Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I) +
        (((-1 / 2 : ℂ) + t * Complex.I))⁻¹ := by
  have hs : ∀ m : ℕ, ((-1 / 2 : ℂ) + t * Complex.I) ≠ -(m : ℂ) := by
    intro m hm
    exact left_point_mem_integerComplement t ⟨-(m : ℤ), by rw [hm]; push_cast; ring⟩
  have h1 := Complex.digamma_apply_add_one ((-1 / 2 : ℂ) + t * Complex.I) hs
  have e1 : ((-1 / 2 : ℂ) + t * Complex.I) + 1 = (1 / 2 : ℂ) + t * Complex.I := by
    push_cast
    ring
  rwa [e1] at h1

/-- The imaginary part of `ψ(-1/2 + i t)`. -/
private theorem digamma_left_im (t : ℝ) :
    (Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)).im
      = π / 2 * Real.tanh (π * t) + t / (1 / 4 + t ^ 2) := by
  have hs := digamma_left_shift t
  have him : (Complex.digamma ((1 / 2 : ℂ) + t * Complex.I)).im
      = (Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)).im +
        ((((-1 / 2 : ℂ) + t * Complex.I))⁻¹).im := by
    have h := congrArg Complex.im hs
    simpa only [Complex.add_im] using h
  rw [inv_left_im t, digamma_half_im_eq t] at him
  have hh : -t / (1 / 4 + t ^ 2) = -(t / (1 / 4 + t ^ 2)) := by ring
  rw [hh] at him
  linarith

/-- The real part of `ψ(-1/2 + i t)` is at least `-5/4`. -/
private theorem digamma_left_re_lb (t : ℝ) (ht : 2 ≤ |t|) :
    -(5 / 4) ≤ (Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)).re := by
  have hs := digamma_left_shift t
  have hre : (Complex.digamma ((1 / 2 : ℂ) + t * Complex.I)).re
      = (Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)).re +
        ((((-1 / 2 : ℂ) + t * Complex.I))⁻¹).re := by
    have h := congrArg Complex.re hs
    simpa only [Complex.add_re] using h
  rw [inv_left_re t] at hre
  have h1 := digamma_half_re_ge t ht
  have hpos : (0:ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hnn : 0 ≤ (1 / 2) / (1 / 4 + t ^ 2) := div_nonneg (by norm_num) hpos.le
  have heq : -(1 / 2) / (1 / 4 + t ^ 2) = -((1 / 2) / (1 / 4 + t ^ 2)) := by ring
  linarith [hre, h1, hnn, heq]

/-- The real part of `ψ(-1/2 + i t)` is at most `log t + 1` from height five. -/
private theorem digamma_left_re_ub (t : ℝ) (ht : 5 ≤ t) :
    (Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)).re ≤ Real.log t + 5 / 4 := by
  have hs := digamma_left_shift t
  have hre : (Complex.digamma ((1 / 2 : ℂ) + t * Complex.I)).re
      = (Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)).re +
        ((((-1 / 2 : ℂ) + t * Complex.I))⁻¹).re := by
    have h := congrArg Complex.re hs
    simpa only [Complex.add_re] using h
  rw [inv_left_re t] at hre
  have h1 := digamma_half_re_le t (by rw [abs_of_nonneg (by linarith)]; linarith)
  have ht0 : (0:ℝ) < t := by linarith
  have h3 : Real.log (|t| + 3) ≤ Real.log t + 4 / 5 := by
    have h4 : |t| + 3 ≤ t * (9 / 5) := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h5 : Real.log (t * (9 / 5)) = Real.log t + Real.log (9 / 5) :=
      Real.log_mul (ne_of_gt ht0) (by norm_num)
    have h6 : Real.log (9 / 5) ≤ 4 / 5 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 9 / 5)
      linarith
    calc Real.log (|t| + 3) ≤ Real.log (t * (9 / 5)) :=
          Real.log_le_log (by positivity) h4
      _ = Real.log t + Real.log (9 / 5) := h5
      _ ≤ Real.log t + 4 / 5 := by linarith
  rw [abs_of_nonneg (by linarith)] at h1
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t)] at h3
  have hpos : (0:ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hhalf : (1 / 2) / (1 / 4 + t ^ 2) ≤ 1 / 5 := by
    rw [div_le_iff₀ hpos]
    have h1 : (0:ℝ) ≤ t * (t - 5) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1]
  have heq : -(1 / 2) / (1 / 4 + t ^ 2) = -((1 / 2) / (1 / 4 + t ^ 2)) := by ring
  linarith [hre, h1, hhalf, heq]

/-- `log 4 ≤ log t` gives the room the numerical budget needs at height five. -/
private theorem log_four_le_log (t : ℝ) (ht : 4 ≤ t) : Real.log 4 ≤ Real.log t :=
  Real.log_le_log (by norm_num) ht

/-- `1.35 ≤ log t` for `t > 5`. -/
private theorem log_gt_one_35 (t : ℝ) (ht : 5 < t) : (1.35 : ℝ) ≤ Real.log t := by
  have h4 : Real.log 4 ≤ Real.log t := log_four_le_log t (by linarith)
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 := Real.log_two_gt_d9
  rw [h42] at h4
  linarith

/-- The pointwise bound for the logarithmic derivative of zeta on the left line. -/
private theorem left_logDeriv_le (t : ℝ) (ht : 5 < t) :
    ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log t + 87 / 20 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hsint : ∀ n : ℤ, ((-1 / 2 : ℂ) + t * Complex.I) ≠ n := by
    intro n hn
    exact left_point_mem_integerComplement t ⟨n, hn.symm⟩
  have hz : riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) ≠ 0 := by
    simpa using LeanLab.PNTPort.ZetaZeros.zeta_left_ne t
  have hFE := logDeriv_riemannZeta_one_sub hsint hz
  have hA : ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * Complex.I))‖ ≤ 19 / 10 := by
    have e : (1 : ℂ) - ((-1 / 2 : ℂ) + t * Complex.I)
        = (((3 / 2 : ℝ)) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e]
    exact zeta_three_half_bound (-t)
  have hlogre : (Complex.log (2 * π)).re = Real.log (2 * π) := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.ofReal_re]
  have hlogim : (Complex.log (2 * π)).im = 0 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.ofReal_im]
  have hpsi_im := digamma_left_im t
  have hpsi_ub := digamma_left_re_ub t (le_of_lt ht)
  have hpsi_lb := digamma_left_re_lb t (by
    rw [abs_of_nonneg (by linarith)]
    linarith)
  have htan_im := tan_left_im t
  have htan := tan_left_re_bounds t (le_of_lt ht)
  set W : ℂ := Complex.log (2 * π) - Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I) +
    π / 2 * Complex.tan (π * ((-1 / 2 : ℂ) + t * Complex.I) / 2) with hWdef
  have hWim : W.im = -t / (1 / 4 + t ^ 2) := by
    rw [hWdef]
    simp only [Complex.sub_im, Complex.add_im, hlogim, hpsi_im, htan_im]
    ring
  have hWre_ub : W.re ≤ 2 + 5 / 4 := by
    rw [hWdef]
    simp only [Complex.sub_re, Complex.add_re, hlogre]
    have h2 := LeanLab.PNTPort.ZetaZeros.log_two_pi_le
    linarith [htan.2, hpsi_lb]
  have hWre_lb : -(W.re) ≤ Real.log t + 2.2 := by
    rw [hWdef]
    simp only [Complex.sub_re, Complex.add_re, hlogre]
    have h2 : (0:ℝ) ≤ Real.log (2 * π) :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have h3 := htan.1
    linarith [hpsi_ub]
  have hlog5 : (1 : ℝ) ≤ Real.log t := by linarith [log_gt_one_35 t ht]
  have hWre : |W.re| ≤ Real.log t + 9 / 4 := by
    rw [abs_le]
    constructor
    · linarith [hWre_lb]
    · linarith [hWre_ub, hlog5]
  have hWim_abs : |W.im| ≤ 1 / 5 := by
    rw [hWim, abs_div, abs_neg, abs_of_nonneg (le_of_lt ht0),
      abs_of_pos (by positivity : (0:ℝ) < 1 / 4 + t ^ 2)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 / 4 + t ^ 2)]
    have h1 : (0:ℝ) ≤ t * (t - 5) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1]
  have hW : ‖W‖ ≤ Real.log t + 9 / 4 + 1 / 5 := by
    calc ‖W‖ ≤ |W.re| + |W.im| := Complex.norm_le_abs_re_add_abs_im W
      _ ≤ (Real.log t + 9 / 4) + 1 / 5 := by linarith [hWre, hWim_abs]
  rw [hFE]
  have hgroup : -logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * Complex.I)) +
        Complex.log (2 * π) - Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I) +
        π / 2 * Complex.tan (π * ((-1 / 2 : ℂ) + t * Complex.I) / 2)
      = -logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * Complex.I)) + W := by
    rw [hWdef]
    ring
  rw [hgroup]
  calc ‖-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * Complex.I)) + W‖
      ≤ ‖logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * Complex.I))‖ + ‖W‖ := by
        simpa using norm_add_le (-logDeriv riemannZeta (1 - ((-1 / 2 : ℂ) + t * Complex.I))) W
    _ ≤ 19 / 10 + (Real.log t + 9 / 4 + 1 / 5) := by linarith [hA, hW]
    _ = Real.log t + 87 / 20 := by ring

/-- LEAF. The pointwise square bound on the positive tail: for `5 < t` the square of the
logarithmic derivative weight is at most the elementary majorant `(2 log t + 3) ^ 2 / t ^ 2`.
This is the analytic step, the size of `logDeriv riemannZeta` at `-1/2 + i t` against the size of
`-1/2 + i t`, and it carries all the arithmetic content of the bound. -/
theorem tail_pos_pointwise_sq (t : ℝ) (ht : 5 < t) :
    ‖principalLogWeight t‖ ^ 2 ≤ (2 * Real.log t + 3) ^ 2 / t ^ 2 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hL := left_logDeriv_le t ht
  have h35 := log_gt_one_35 t ht
  have hroom : Real.log t + 87 / 20 ≤ 2 * Real.log t + 3 := by linarith
  have hnn : (0 : ℝ) ≤ Real.log t + 87 / 20 := by linarith
  have hsnorm : t ≤ ‖((-1 / 2 : ℂ) + t * Complex.I)‖ := by
    have hsq : ‖((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    nlinarith [norm_nonneg ((-1 / 2 : ℂ) + t * Complex.I)]
  have hinv : (‖((-1 / 2 : ℂ) + t * Complex.I)‖)⁻¹ ≤ t⁻¹ := by
    rw [← one_div, ← one_div]
    exact div_le_div_of_nonneg_left (by norm_num) ht0 hsnorm
  have hstep : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ *
      (‖((-1 / 2 : ℂ) + t * Complex.I)‖)⁻¹ ≤ (Real.log t + 87 / 20) * t⁻¹ :=
    mul_le_mul hL hinv (by positivity) hnn
  rw [principalLogWeight, norm_div, div_eq_mul_inv, mul_pow]
  have h2 : ((Real.log t + 87 / 20) * t⁻¹) ^ 2 ≤ ((2 * Real.log t + 3) * t⁻¹) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hroom (by positivity)
  calc ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 *
        (‖((-1 / 2 : ℂ) + t * Complex.I)‖⁻¹) ^ 2
      = (‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ *
        (‖((-1 / 2 : ℂ) + t * Complex.I)‖)⁻¹) ^ 2 := by ring
    _ ≤ ((Real.log t + 87 / 20) * t⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hstep 2
    _ ≤ ((2 * Real.log t + 3) * t⁻¹) ^ 2 := h2
    _ = (2 * Real.log t + 3) ^ 2 / t ^ 2 := by
        rw [div_eq_mul_inv, mul_pow, inv_pow]


/-- LEAF. Integrability of the majorant on the near piece `5 < t ≤ 8`.  The majorant is dominated
by a negative power of `t`, so it is integrable on the short interval; this is the hypothesis that
lets the near piece be compared with the weight. -/
theorem tail_pos_majorant_integrableOn_head :
    IntegrableOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioc 5 8) := by
  have hcont : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Icc 5 8) := by
    have hlog : ContinuousOn Real.log (Set.Icc (5 : ℝ) 8) :=
      Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : (5 : ℝ) ≤ x := hx.1
        rintro rfl
        norm_num at h1)
    have hnum : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2) (Set.Icc (5 : ℝ) 8) :=
      ((hlog.const_mul 2).add continuousOn_const).pow 2
    exact hnum.div (continuousOn_id.pow 2) (by
      intro x hx
      have h1 : (5 : ℝ) ≤ x := hx.1
      intro h
      have hx0 : x = 0 := sq_eq_zero_iff.mp h
      linarith)
  exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

/-- The power `t ^ (1/2)` divided by `t ^ 2` is `t ^ (-(3/2))`. -/
private lemma tail_pos_rpow_half_div_sq (t : ℝ) (ht : 0 < t) :
    t ^ (1 / 2 : ℝ) / t ^ 2 = t ^ (-(3 / 2) : ℝ) := by
  rw [div_eq_mul_inv, show (t ^ 2 : ℝ) = t ^ (2 : ℝ) by rw [Real.rpow_two],
    ← Real.rpow_neg ht.le (2 : ℝ), ← Real.rpow_add ht]
  norm_num

/-- The pointwise domination of the majorant by `121 t ^ (-(3/2))` on `8 < t`.  The logarithm
is paid for by a fourth root, which leaves the negative power `-(3/2)` of `t` behind. -/
private lemma tail_pos_majorant_le_rpow (t : ℝ) (ht : 8 < t) :
    (2 * Real.log t + 3) ^ 2 / t ^ 2 ≤ 121 * t ^ (-(3 / 2) : ℝ) := by
  have ht0 : 0 < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlog4 : Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 4)
    calc Real.log t ≤ t ^ (1 / 4 : ℝ) / (1 / 4) := h
      _ = 4 * t ^ (1 / 4 : ℝ) := by ring
  have hpow1 : (1 : ℝ) ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hlogpos : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hb : 2 * Real.log t + 3 ≤ 11 * t ^ (1 / 4 : ℝ) := by nlinarith
  have hb0 : 0 ≤ 2 * Real.log t + 3 := by linarith
  have hsq : (11 * t ^ (1 / 4 : ℝ)) ^ 2 = 121 * t ^ (1 / 2 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast ht0.le]
    norm_num
  have hsqle : (2 * Real.log t + 3) ^ 2 ≤ 121 * t ^ (1 / 2 : ℝ) := by
    nlinarith [hb, hb0, hsq, sq_nonneg (11 * t ^ (1 / 4 : ℝ)),
      sq_nonneg (2 * Real.log t + 3 - 11 * t ^ (1 / 4 : ℝ))]
  have hstep : (2 * Real.log t + 3) ^ 2 / t ^ 2 ≤ 121 * t ^ (1 / 2 : ℝ) / t ^ 2 :=
    div_le_div_of_nonneg_right hsqle (by positivity)
  have heq : 121 * t ^ (1 / 2 : ℝ) / t ^ 2 = 121 * t ^ (-(3 / 2) : ℝ) := by
    rw [show 121 * t ^ (1 / 2 : ℝ) / t ^ 2 = 121 * (t ^ (1 / 2 : ℝ) / t ^ 2) by ring,
      tail_pos_rpow_half_div_sq t ht0]
  linarith [hstep, heq.le, heq.ge]

/-- LEAF. Integrability of the majorant on the far piece `8 < t`.  Here the decay of the majorant
is what is paid for, and again a negative power of `t` dominates it; this is the hypothesis that
lets the far piece be compared with the weight. -/
theorem tail_pos_majorant_integrableOn_far :
    IntegrableOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioi 8) := by
  have hmaj : IntegrableOn (fun t : ℝ => 121 * t ^ (-(3 / 2) : ℝ)) (Set.Ioi 8) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-(3 / 2) : ℝ)) (c := 8) (by norm_num)
      (by norm_num)).const_mul 121
  have hcont : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioi 8) := by
    have hlog : ContinuousOn Real.log (Set.Ioi (8 : ℝ)) :=
      Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : (8 : ℝ) < x := hx
        rintro rfl
        norm_num at h1)
    have hnum : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2) (Set.Ioi (8 : ℝ)) :=
      ((hlog.const_mul 2).add continuousOn_const).pow 2
    exact hnum.div (continuousOn_id.pow 2) (by
      intro x hx
      have h1 : (8 : ℝ) < x := hx
      intro h
      have hx0 : x = 0 := sq_eq_zero_iff.mp h
      linarith)
  refine Integrable.mono' hmaj (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hnn : (0 : ℝ) ≤ (2 * Real.log t + 3) ^ 2 / t ^ 2 := by
    have h1 : (0 : ℝ) < t := by linarith [Set.mem_Ioi.mp ht]
    positivity
  rw [Real.norm_of_nonneg hnn]
  exact tail_pos_majorant_le_rpow t ht

/-- The primitive of the majorant: differentiating `-((2 log t)^2 + 20 log t + 29) / t` gives
`(2 log t + 3)^2 / t^2`. -/
private lemma hasDerivAt_tail_pos_primitive (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => -(((2 * Real.log s) ^ 2 + 20 * Real.log s + 29) / s))
      ((2 * Real.log t + 3) ^ 2 / t ^ 2) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.log s) (2 * t⁻¹) t := hlog.const_mul 2
  have h4 : HasDerivAt (fun s : ℝ => 20 * Real.log s) (20 * t⁻¹) t := hlog.const_mul 20
  have hA := ((h2.pow 2).add h4).add_const 29
  have hq := hA.div (hasDerivAt_id t) ht.ne'
  refine (hq.neg).congr_deriv ?_
  norm_num
  field_simp
  ring

/-- The logarithm squared over the identity tends to zero. -/
private lemma tail_pos_tendsto_log_sq_div (n : ℕ) :
    Filter.Tendsto (fun t : ℝ => Real.log t ^ n / t) Filter.atTop (nhds 0) :=
  (Real.isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero

/-- The primitive of the majorant tends to zero at infinity. -/
private lemma tendsto_tail_pos_primitive :
    Filter.Tendsto (fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t)) Filter.atTop (nhds 0) := by
  have h2 : Filter.Tendsto (fun t : ℝ => (2 * Real.log t) ^ 2 / t) Filter.atTop (nhds 0) := by
    have hbase := (tail_pos_tendsto_log_sq_div 2).const_mul (4 : ℝ)
    have hfun : (fun t : ℝ => (2 * Real.log t) ^ 2 / t)
        = fun t : ℝ => 4 * (Real.log t ^ 2 / t) := by
      funext t
      ring
    rw [hfun]
    simpa using hbase
  have h20 : Filter.Tendsto (fun t : ℝ => 20 * Real.log t / t) Filter.atTop (nhds 0) := by
    have hbase := (tail_pos_tendsto_log_sq_div 1).const_mul (20 : ℝ)
    have hfun : (fun t : ℝ => 20 * Real.log t / t)
        = fun t : ℝ => 20 * (Real.log t ^ 1 / t) := by
      funext t
      ring
    rw [hfun]
    simpa using hbase
  have h29 : Filter.Tendsto (fun t : ℝ => 29 / t) Filter.atTop (nhds 0) := by
    have hbase := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (29 : ℝ)
    have hfun : (fun t : ℝ => 29 / t) = fun t : ℝ => 29 * t⁻¹ := by
      funext t
      rw [div_eq_mul_inv]
    rw [hfun]
    simpa using hbase
  have hsum := ((h2.add h20).add h29).neg
  have hfun : (fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
      = fun t : ℝ => -((2 * Real.log t) ^ 2 / t + 20 * Real.log t / t + 29 / t) := by
    funext t
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
  rw [hfun]
  simpa using hsum

/-- The value of the majorant integral on the far piece, from the primitive. -/
private lemma integral_tail_pos_far :
    (∫ t in Set.Ioi (8 : ℝ), (2 * Real.log t + 3) ^ 2 / t ^ 2)
      = (4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29) / 8 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
    (f' := fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (a := 8) (m := 0)
    (fun x hx => hasDerivAt_tail_pos_primitive x (by linarith [Set.mem_Ici.mp hx]))
    tail_pos_majorant_integrableOn_far tendsto_tail_pos_primitive
  rw [h]
  ring

/-- The value of the majorant integral on the near piece, from the primitive. -/
private lemma integral_tail_pos_head :
    (∫ t in Set.Ioc (5 : ℝ) 8, (2 * Real.log t + 3) ^ 2 / t ^ 2)
      = (4 * (Real.log 5) ^ 2 + 20 * Real.log 5 + 29) / 5 -
        (4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29) / 8 := by
  have hle : (5 : ℝ) ≤ 8 := by norm_num
  rw [← intervalIntegral.integral_of_le hle]
  have hint : IntervalIntegrable (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) volume 5 8 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr tail_pos_majorant_integrableOn_head
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
    (f' := fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (a := 5) (b := 8)
    (fun x hx => hasDerivAt_tail_pos_primitive x (by
      rw [Set.uIcc_of_le hle] at hx
      have h1 : (5 : ℝ) ≤ x := hx.1
      linarith))
    hint
  rw [h]
  ring

/-- The logarithm of five is at most `1.637`, from `log 5 = log (5/4) + 2 log 2`. -/
private lemma tail_pos_log_five_le : Real.log 5 ≤ 1.637 := by
  have hsplit : Real.log 5 = Real.log (5 / 4) + Real.log 4 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h54 : Real.log (5 / 4) ≤ 5 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  nlinarith [Real.log_two_lt_d9, hsplit, h54, h4]

/-- The logarithm of eight is three times the logarithm of two. -/
private lemma tail_pos_log_eight_eq : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  ring

/-- The elementary majorant at `log 8` is at most `128`. -/
private lemma tail_pos_A_log_eight_upper :
    4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29 ≤ 128 := by
  have heq := tail_pos_log_eight_eq
  have h1 : Real.log 8 ≤ 3 * 0.6931471808 := by
    rw [heq]
    nlinarith [Real.log_two_lt_d9]
  have h0 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- The elementary majorant at `log 8` is at least `87.8`. -/
private lemma tail_pos_A_log_eight_lower :
    87.8 ≤ 4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29 := by
  have heq := tail_pos_log_eight_eq
  have h1 : 3 * 0.6931471803 ≤ Real.log 8 := by
    rw [heq]
    nlinarith [Real.log_two_gt_d9]
  have h0 : 0 ≤ Real.log 8 := le_trans (by norm_num) h1
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- The elementary majorant at `log 5` is at most `72.5`. -/
private lemma tail_pos_A_log_five_upper :
    4 * (Real.log 5) ^ 2 + 20 * Real.log 5 + 29 ≤ 72.5 := by
  have h1 : Real.log 5 ≤ 1.637 := tail_pos_log_five_le
  have h0 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- LEAF. The numerical value of the near piece: the integral of the majorant over `5 < t ≤ 8` is
at most four.  The primitive is `-((2 log t) ^ 2 + 20 log t + 29) / t`, which gives the value
`3.322` for this piece, and the budget four leaves room. -/
theorem tail_pos_majorant_head_le :
    (∫ t in Set.Ioc 5 8, (2 * Real.log t + 3) ^ 2 / t ^ 2) ≤ 4 := by
  rw [integral_tail_pos_head]
  have h5 := tail_pos_A_log_five_upper
  have h8 := tail_pos_A_log_eight_lower
  linarith

/-- LEAF. The numerical value of the far piece: the integral of the majorant over `8 < t` is at
most sixteen.  The same primitive gives the value `10.988` for this piece, and the budget sixteen
leaves room. -/
theorem tail_pos_majorant_far_le :
    (∫ t in Set.Ioi 8, (2 * Real.log t + 3) ^ 2 / t ^ 2) ≤ 16 := by
  rw [integral_tail_pos_far]
  have h8 := tail_pos_A_log_eight_upper
  linarith

/-- The positive tail `5 < t` splits at height eight into the near piece and the far piece. -/
private theorem tail_pos_region :
    (Set.Ioi (5 : ℝ)) = Set.Ioc 5 8 ∪ Set.Ioi 8 := by
  ext t
  simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
  constructor
  · intro h
    by_cases h8 : t ≤ 8
    · exact Or.inl ⟨h, h8⟩
    · exact Or.inr (by linarith)
  · rintro (⟨h, _⟩ | h)
    · exact h
    · linarith

/-- The two pieces of the positive tail are disjoint. -/
private theorem tail_pos_disjoint :
    Disjoint (Set.Ioc (5 : ℝ) 8) (Set.Ioi 8) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [Set.mem_Ioc] at hx
  rw [Set.mem_Ioi] at hx'
  linarith

/-- The square energy over the positive tail is the sum of the energies over the two pieces.  The
pieces are disjoint and measurable and the squared weight is integrable, so the integral splits. -/
private theorem tail_pos_decomp :
    (∫ t in Set.Ioi (5 : ℝ), ‖principalLogWeight t‖ ^ 2) =
      (∫ t in Set.Ioc 5 8, ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Ioi 8, ‖principalLogWeight t‖ ^ 2) := by
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  rw [tail_pos_region,
    setIntegral_union tail_pos_disjoint measurableSet_Ioi hint.integrableOn hint.integrableOn]

/-- The square energy of the logarithmic derivative weight on the positive tail `5 < t` is at most
twenty.  The tail is cut at height eight, each piece is compared with the elementary majorant
using the pointwise bound, and the two numerical integrals four and sixteen add up to twenty. -/
theorem principal_log_weight_sq_tail_pos_split :
    (∫ t in Set.Ioi 5, ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  classical
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hhead : (∫ t in Set.Ioc 5 8, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioc 5 8, (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
    setIntegral_mono_on hint.integrableOn tail_pos_majorant_integrableOn_head measurableSet_Ioc
      (fun t ht => tail_pos_pointwise_sq t (Set.mem_Ioc.mp ht).1)
  have hfar : (∫ t in Set.Ioi 8, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioi 8, (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
    setIntegral_mono_on hint.integrableOn tail_pos_majorant_integrableOn_far measurableSet_Ioi
      (fun t ht => tail_pos_pointwise_sq t (by linarith [Set.mem_Ioi.mp ht]))
  rw [tail_pos_decomp]
  linarith [hhead, hfar, tail_pos_majorant_head_le, tail_pos_majorant_far_le]

end LeanLab.HelfgottMajor.Decomp457b

import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long
import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_tail_neg_digamma_envelope

/-!
Splitting the negative tail square energy of the logarithmic derivative weight,
`Decomp457b.principal_log_weight_sq_tail_neg`, which bounds the square energy on the half
line `t < -5` by twenty.

The weight is the logarithmic derivative of the Riemann zeta function at `-1/2 + it`
divided by `-1/2 + it`, so its square is the square modulus of that logarithmic derivative
divided by `1/4 + t ^ 2`.  On `t < -5` the denominator is at least `t ^ 2`, and the
logarithmic derivative is at most the envelope `log |t| + 7`; the square of the envelope
over `t ^ 2` is an elementary integral on `(5, ∞)` whose value is
`(log 5 ^ 2 + 16 log 5 + 65) / 5`, and that number is below twenty since `log 5 ≤ 1.7`.

The envelope is not available as a single estimate in the library, so it is cut into the
two inputs that the functional equation needs: the logarithmic derivative on the line of
real part three halves, where the Dirichlet series makes the real point the largest one,
and the digamma function on the line of real part minus one half, which is the growth of
the gamma factor.  The functional equation
`z'/z(s) = -z'/z(1-s) + log 2 pi - psi(s) + (pi/2) tan(pi s/2)`, the exact modulus
`‖tan(-pi/4 + i y)‖ ≤ 1`, `log 2 pi ≤ 2` and `pi/2 ≤ 1.571` turn those two inputs into the
envelope, with the constant `19/10 + 2 + 3/2 + 1.571 ≤ 7`.  That chain, the comparison of
the weight with the envelope, the integrability of the weight and the addition of the
three pieces into the budget twenty are all proved below; only the three steps stated as
leaves remain open.

No prime sum, no zero sum and no scale appears in the statement of any leaf.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

open Filter
open scoped Topology

/-- LEAF. The digamma input. The modulus of the digamma function on the line of real part
minus one half is at most `log |t| + 3/2` from height two on. This is the growth step of the
gamma factor in the functional equation, and it is the piece that no series expansion in
the library supplies. -/
theorem principal_log_weight_tail_neg_digamma_envelope (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 3 / 2 := by
  exact principal_log_weight_tail_neg_digamma_envelope_of_leaves t ht


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
theorem principal_log_weight_tail_neg_zeta_three_halves (y : ℝ) :
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


/-! ### Auxiliary lemmas for the elementary tail integral

`(log x + 7) ^ 2 / x ^ 2` has the primitive `-((log x) ^ 2 + 16 log x + 65) / x` on the
positive axis, because `P - P' = (log x + 7) ^ 2` for `P = A ^ 2 + 16 A + 65` and `A = log x`.
The primitive tends to zero at infinity, the squared envelope is dominated by `121 / x ^ (3/2)`,
and `log 5 ≤ 1.61`, so the integral on `(5, ∞)` is at most `(1.61 ^ 2 + 16 * 1.61 + 65) / 5 < 20`.
-/

/-- `log 5 ≤ 1.61`. -/
private theorem log_five_le_tail_neg : Real.log 5 ≤ 1.61 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 11, (1.61 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.61 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- The primitive of `(log x + 7) ^ 2 / x ^ 2` on the positive axis. -/
private theorem hasDerivAt_tail_neg_primitive (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -((Real.log y) ^ 2 + 16 * Real.log y + 65) / y)
      ((Real.log x + 7) ^ 2 / x ^ 2) x := by
  have hL : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hmul : HasDerivAt (fun y : ℝ => Real.log y * Real.log y)
      (x⁻¹ * Real.log x + Real.log x * x⁻¹) x := hL.mul hL
  have hN : HasDerivAt (fun y : ℝ => Real.log y * Real.log y + 16 * Real.log y + 65)
      (x⁻¹ * Real.log x + Real.log x * x⁻¹ + 16 * x⁻¹) x := by
    have h1 : HasDerivAt (fun y : ℝ => Real.log y * Real.log y + 16 * Real.log y)
        (x⁻¹ * Real.log x + Real.log x * x⁻¹ + 16 * x⁻¹) x :=
      hmul.add (hL.const_mul 16)
    exact h1.add_const 65
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx.ne'
  have h := hN.neg.mul hinv
  have hxne : x ≠ 0 := hx.ne'
  convert h using 1
  · funext y
    simp only [Pi.mul_apply, Pi.neg_apply]
    ring
  · field_simp
    simp only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    ring

/-- The primitive tends to `0` at infinity. -/
private theorem tendsto_tail_neg_primitive :
    Tendsto (fun y : ℝ => -((Real.log y) ^ 2 + 16 * Real.log y + 65) / y) atTop (𝓝 0) := by
  have h12 : Tendsto (fun y : ℝ => Real.log y / y ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hs : Tendsto (fun y : ℝ => (Real.log y) ^ 2 / y) atTop (𝓝 0) := by
    have h2 : Tendsto (fun y : ℝ => (Real.log y / y ^ (1 / 2 : ℝ)) ^ 2) atTop (𝓝 0) := by
      simpa using h12.pow 2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (le_of_lt hy)]
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hev : (fun y : ℝ => -((Real.log y) ^ 2 + 16 * Real.log y + 65) / y)
      =ᶠ[atTop] fun y =>
        -((Real.log y) ^ 2 / y) - 16 * (Real.log y / y) - 65 * y⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    field_simp
    ring
  rw [Filter.tendsto_congr' hev]
  have hfin := ((hs.neg).sub (h1.const_mul 16)).sub (hinv.const_mul 65)
  simpa using hfin

/-- Integrability of the squared envelope on `(5, ∞)`, dominated by `121 / x ^ (3/2)`. -/
private theorem integrableOn_tail_neg_envelope :
    IntegrableOn (fun x : ℝ => (Real.log x + 7) ^ 2 / x ^ 2) (Set.Ioi 5) := by
  have hmaj : IntegrableOn (fun x : ℝ => 121 * x ^ (-(3 / 2) : ℝ)) (Set.Ioi 5) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 5)).const_mul 121
  have hcont : ContinuousOn (fun x : ℝ => (Real.log x + 7) ^ 2 / x ^ 2) (Set.Ioi (5 : ℝ)) := by
    apply ContinuousOn.div
    · refine ContinuousOn.pow ?_ 2
      exact (Real.continuousOn_log.mono (fun y hy => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [Set.mem_Ioi.mp hy])).add continuousOn_const
    · exact ContinuousOn.pow continuousOn_id 2
    · intro x hx
      have hx0 : (0 : ℝ) < x := by linarith [Set.mem_Ioi.mp hx]
      positivity
  refine hmaj.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx5 : (5 : ℝ) < x := Set.mem_Ioi.mp hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have hh := Real.log_le_rpow_div (le_of_lt hx0) (by norm_num : (0 : ℝ) < 1 / 4)
    have h2 : x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) := by ring
    rwa [h2] at hh
  have hpos : (0 : ℝ) ≤ Real.log x + 7 := by
    have := Real.log_pos (by linarith : (1 : ℝ) < x)
    linarith
  have hbound : Real.log x + 7 ≤ 11 * x ^ (1 / 4 : ℝ) := by linarith
  have hsq : (Real.log x + 7) ^ 2 ≤ 121 * x ^ (1 / 2 : ℝ) := by
    have h11 : (0 : ℝ) ≤ 11 * x ^ (1 / 4 : ℝ) := by positivity
    have e : (11 * x ^ (1 / 4 : ℝ)) ^ 2 = 121 * x ^ (1 / 2 : ℝ) := by
      rw [mul_pow,
        show (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) by
          rw [sq, ← Real.rpow_add hx0]
          norm_num]
      norm_num
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (le_of_lt hx0)]
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have e2 : x ^ 2 = x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  rw [div_le_iff₀ hx2, e2]
  have e3 : 121 * (x ^ (3 / 2 : ℝ))⁻¹ * (x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ))
      = 121 * x ^ (1 / 2 : ℝ) := by
    field_simp
  rw [e3]
  exact hsq

/-- `∫_5^∞ (log x + 7)^2 / x^2 ≤ 20`. -/
private theorem integral_Ioi_five_tail_neg_envelope :
    ∫ x in Set.Ioi (5 : ℝ), (Real.log x + 7) ^ 2 / x ^ 2 ≤ 20 := by
  have hderiv : ∀ x ∈ Set.Ici (5 : ℝ),
      HasDerivAt (fun y : ℝ => -((Real.log y) ^ 2 + 16 * Real.log y + 65) / y)
        ((Real.log x + 7) ^ 2 / x ^ 2) x :=
    fun x hx => hasDerivAt_tail_neg_primitive x (by linarith [Set.mem_Ici.mp hx])
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv integrableOn_tail_neg_envelope
    tendsto_tail_neg_primitive
  rw [key]
  have hlog := log_five_le_tail_neg
  have hpos5 : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)
  have e : (0 : ℝ) - -((Real.log 5) ^ 2 + 16 * Real.log 5 + 65) / 5
      = ((Real.log 5) ^ 2 + 16 * Real.log 5 + 65) / 5 := by ring
  rw [e]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)]
  nlinarith

/-- LEAF. The elementary integral. The envelope squared over `t ^ 2` is integrable on the
half line `t < -5`, and its integral there is at most twenty. The integral is elementary,
`∫ t in (5, ∞), (log t + 7) ^ 2 / t ^ 2 = (log 5 ^ 2 + 16 log 5 + 65) / 5`, and that is
below twenty because `log 5 ≤ 1.7`. Both the finiteness and the value are needed below:
the finiteness to compare the two integrands, the value to add up the budget. -/
theorem principal_log_weight_tail_neg_majorant_integral :
    IntegrableOn (fun t : ℝ => (Real.log (-t) + 7) ^ 2 / t ^ 2) (Set.Iio (-5)) ∧
      (∫ t in Set.Iio (-5 : ℝ), (Real.log (-t) + 7) ^ 2 / t ^ 2) ≤ 20 := by
  have hA : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Ioi (5 : ℝ)) = Set.Iio (-5) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  have hint : IntegrableOn (fun t : ℝ => (Real.log (-t) + 7) ^ 2 / t ^ 2) (Set.Iio (-5)) := by
    have hmap := hA.integrableOn_map_iff (μ := volume)
      (f := fun x : ℝ => (Real.log x + 7) ^ 2 / x ^ 2) (s := Set.Ioi (5 : ℝ))
    rw [Measure.map_neg_eq_self (volume : Measure ℝ), hpre] at hmap
    refine (hmap.mp integrableOn_tail_neg_envelope).congr_fun (fun x _ => ?_) measurableSet_Iio
    simp only [Function.comp_apply, neg_sq]
  refine ⟨hint, ?_⟩
  have hsub : (∫ t in Set.Iio (-5 : ℝ), (Real.log (-t) + 7) ^ 2 / t ^ 2)
      = ∫ x in Set.Ioi (5 : ℝ), (Real.log x + 7) ^ 2 / x ^ 2 := by
    have hcomp := integral_comp_neg_Iic (-5 : ℝ)
      (f := fun x : ℝ => (Real.log x + 7) ^ 2 / x ^ 2)
    rw [show (-(-5) : ℝ) = 5 by norm_num] at hcomp
    rw [← integral_Iic_eq_integral_Iio (x := (-5 : ℝ))
      (f := fun t : ℝ => (Real.log (-t) + 7) ^ 2 / t ^ 2)]
    refine (setIntegral_congr_fun measurableSet_Iic (fun x _ => ?_)).trans hcomp
    simp only [Function.comp_apply, neg_sq]
  rw [hsub]
  exact integral_Ioi_five_tail_neg_envelope

/-- The squared norm of the weight, as the square modulus of the logarithmic derivative of
zeta on the left contour divided by `1/4 + t ^ 2`. -/
private theorem norm_principalLogWeight_sq (t : ℝ) :
    ‖principalLogWeight t‖ ^ 2 =
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 / (1 / 4 + t ^ 2) := by
  have hs : ‖((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [principalLogWeight, norm_div, div_pow, hs]

/-- `‖tan(-pi/4 + i y)‖ ≤ 1`: at real part `-pi/4` the sine and the cosine have real and
imaginary parts of equal size, so the modulus of their quotient is one. -/
private theorem norm_tan_neg_pi_div_four_le (y : ℝ) :
    ‖Complex.tan ((-(π / 4) : ℝ) + y * Complex.I)‖ ≤ 1 := by
  set x : ℝ := -(π / 4) with hx
  have hsx : Real.sin x ^ 2 = 1 / 2 := by
    rw [hx, Real.sin_neg, Real.sin_pi_div_four, neg_sq, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hcx : Real.cos x ^ 2 = 1 / 2 := by
    rw [hx, Real.cos_neg, Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hcos : Complex.cos (x + y * Complex.I) =
      ((Real.cos x * Real.cosh y : ℝ) : ℂ) + ((-(Real.sin x * Real.sinh y) : ℝ) : ℂ) *
        Complex.I := by
    rw [Complex.cos_add_mul_I]; push_cast; ring
  have hsin : Complex.sin (x + y * Complex.I) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) *
        Complex.I := by
    rw [Complex.sin_add_mul_I]; push_cast; ring
  have hnc : ‖Complex.cos (x + y * Complex.I)‖ ^ 2 =
      (Real.cosh y ^ 2 + Real.sinh y ^ 2) / 2 := by
    rw [hcos, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    ring_nf
    rw [hsx, hcx]; ring
  have hns : ‖Complex.sin (x + y * Complex.I)‖ ^ 2 =
      (Real.cosh y ^ 2 + Real.sinh y ^ 2) / 2 := by
    rw [hsin, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    ring_nf
    rw [hsx, hcx]; ring
  have hcpos : 0 < ‖Complex.cos (x + y * Complex.I)‖ := by
    have h1 : (0 : ℝ) < ‖Complex.cos (x + y * Complex.I)‖ ^ 2 := by
      rw [hnc]
      have hc := Real.one_le_cosh y
      have hs := sq_nonneg (Real.sinh y)
      nlinarith
    nlinarith [norm_nonneg (Complex.cos (x + y * Complex.I))]
  have heq : ‖Complex.sin (x + y * Complex.I)‖ = ‖Complex.cos (x + y * Complex.I)‖ := by
    have h := hns.trans hnc.symm
    have h2 : Real.sqrt (‖Complex.sin (x + y * Complex.I)‖ ^ 2) =
        Real.sqrt (‖Complex.cos (x + y * Complex.I)‖ ^ 2) := by rw [h]
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2
  rw [Complex.tan_eq_sin_div_cos, norm_div, div_le_one hcpos]
  exact le_of_eq heq

/-- The envelope on the left line from the two inputs. The chain is the functional equation
of `zeta'/zeta`, the exact modulus of `tan` at real part `-pi/4`, `log 2 pi ≤ 2`, `pi/2` at
most `1.571` and the triangle inequality, which give `19/10 + 2 + 3/2 + 1.571 ≤ 7`. -/
private theorem logDeriv_left_line_pointwise_seven
    (hzeta : ∀ y : ℝ,
      ‖logDeriv riemannZeta ((((3 / 2 : ℝ)) : ℂ) + y * Complex.I)‖ ≤ 19 / 10)
    (hpsi : ∀ t : ℝ, 2 ≤ |t| →
      ‖Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 3 / 2)
    (t : ℝ) (ht : 2 ≤ |t|) :
    ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 7 := by
  set s : ℂ := (-1 / 2 : ℂ) + t * Complex.I with hsdef
  have hsim : s.im = t := by simp [hsdef]
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n hn
    have h := congr_arg Complex.im hn
    rw [hsim] at h
    simp only [Complex.intCast_im] at h
    rw [h] at ht
    norm_num at ht
  have hz : riemannZeta s ≠ 0 := by
    have h := LeanLab.PNTPort.ZetaZeros.zeta_left_ne t
    rw [hsdef]
    convert h using 1
    push_cast
    ring
  have hFE := logDeriv_riemannZeta_one_sub (s := s) hint hz
  have hA : ‖logDeriv riemannZeta (1 - s)‖ ≤ 19 / 10 := by
    have e : 1 - s = (((3 / 2 : ℝ)) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
      rw [hsdef]; push_cast; ring
    rw [e]
    exact hzeta (-t)
  have hB : ‖Complex.log (2 * π)‖ ≤ 2 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
    exact LeanLab.PNTPort.ZetaZeros.log_two_pi_le
  have hC : ‖Complex.digamma s‖ ≤ Real.log |t| + 3 / 2 := by
    rw [hsdef]
    exact hpsi t ht
  have hD : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 1.571 := by
    have e : (π : ℂ) * s / 2 = ((-(π / 4) : ℝ) : ℂ) + ((π * t / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hsdef]; push_cast; ring
    rw [e, norm_mul]
    have ht1 := norm_tan_neg_pi_div_four_le (π * t / 2)
    have hp : ‖(π : ℂ) / 2‖ ≤ 1.571 := by
      have h2 : ‖((2 : ℂ))‖ = 2 := by norm_num
      rw [norm_div, h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      have := Real.pi_lt_d6
      linarith
    calc _ ≤ 1.571 * 1 := mul_le_mul hp ht1 (norm_nonneg _) (by norm_num)
      _ = 1.571 := by norm_num
  rw [hFE]
  calc ‖-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s +
        π / 2 * Complex.tan (π * s / 2)‖
      ≤ ‖logDeriv riemannZeta (1 - s)‖ + ‖Complex.log (2 * π)‖ + ‖Complex.digamma s‖ +
        ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add (by rw [norm_neg]) le_rfl))
            le_rfl)) le_rfl)
    _ ≤ 19 / 10 + 2 + (Real.log |t| + 3 / 2) + 1.571 := by gcongr
    _ ≤ Real.log |t| + 7 := by linarith

/-- The negative tail budget, assembled from the three leaves. -/
theorem principal_log_weight_sq_tail_neg_split :
    (∫ t in Set.Iio (-5), ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  obtain ⟨hmajint, hmajval⟩ := principal_log_weight_tail_neg_majorant_integral
  have henv : ∀ t : ℝ, 2 ≤ |t| →
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 7 :=
    logDeriv_left_line_pointwise_seven principal_log_weight_tail_neg_zeta_three_halves
      principal_log_weight_tail_neg_digamma_envelope
  have hintw : IntegrableOn (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) (Set.Iio (-5)) :=
    (MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two
      (by norm_num)).integrableOn
  have hmono : ∀ t ∈ Set.Iio (-5 : ℝ),
      ‖principalLogWeight t‖ ^ 2 ≤ (Real.log (-t) + 7) ^ 2 / t ^ 2 := by
    intro t ht
    have ht5 : t < -5 := ht
    have ht1 : t < 0 := by linarith
    have habs : |t| = -t := abs_of_neg ht1
    have hb := henv t (by rw [habs]; linarith)
    rw [habs] at hb
    have hnn : (0 : ℝ) ≤ ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ := norm_nonneg _
    have h1 : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        (Real.log (-t) + 7) ^ 2 := by
      simpa using pow_le_pow_left₀ hnn hb 2
    rw [norm_principalLogWeight_sq]
    have h2 : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
    have h3 : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 / (1 / 4 + t ^ 2) ≤
        (Real.log (-t) + 7) ^ 2 / (1 / 4 + t ^ 2) :=
      div_le_div_of_nonneg_right h1 h2.le
    have ht2 : (0 : ℝ) < t ^ 2 := by nlinarith
    have h4 : (Real.log (-t) + 7) ^ 2 / (1 / 4 + t ^ 2) ≤ (Real.log (-t) + 7) ^ 2 / t ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) ht2 (by linarith)
    linarith
  exact (setIntegral_mono_on hintw hmajint measurableSet_Iio hmono).trans hmajval

end LeanLab.HelfgottMajor.Decomp457b

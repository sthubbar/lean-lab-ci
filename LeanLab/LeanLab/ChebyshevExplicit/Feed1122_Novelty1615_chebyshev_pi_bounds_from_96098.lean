import Mathlib

/-!
# ChebyshevExplicit, feed 1122 split of `chebyshev_pi_bounds_from_96098`

AI wrote this Lean code. Binary Goldbach is open.

The two sided bound with the constants 0.92129 and 1.10555 from 96098 on is split into
three leaves. The lower half follows from Rosser and Schoenfeld 1962, Corollary 1, display (3.5):
`π x > x / log x` for `x ≥ 17`. The upper half follows, once `log n ≥ 15`, from Rosser and
Schoenfeld 1962, Theorem 1, display (3.2): `π x < x / log x * (1 + 3 / (2 log x))` for `x > 1`,
since `1 + 3/30 = 1.1 ≤ 1.10555`. The remaining range `96098 ≤ n < 3300000` is a finite check,
which the numerics of unit U-1615 cover, tested to 4e6. The assembly below is complete.
-/

namespace LeanLab.ChebyshevExplicit.Novelty1615

/-- LEAF: Rosser and Schoenfeld 1962, Approximate formulas for some functions of prime numbers,
Corollary 1, display (3.5): `x / log x < π x` for `x ≥ 17`, at natural arguments. CITED-LEFT, HARD. -/
theorem rs_pi_gt_div_log (n : ℕ) (hn : 17 ≤ n) :
    (n : ℝ) / Real.log n < (Nat.primeCounting n : ℝ) := by
  sorry

/-- LEAF: Rosser and Schoenfeld 1962, Theorem 1, display (3.2): `π x < x / log x * (1 + 3 / (2 log x))`
for `x > 1`, at natural arguments. CITED-LEFT, HARD. -/
theorem rs_pi_lt_div_log_mul (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) < (n : ℝ) / Real.log n * (1 + 3 / (2 * Real.log n)) := by
  sorry

/-- LEAF: the finite check of the upper half on `96098 ≤ n < 3300000`, the range below the point
where `log n ≥ 15` makes display (3.2) of Rosser and Schoenfeld sufficient. Numerics of unit U-1615:
the last integer with `π n > 1.10555 n / log n` is 96097. HARD, a large verified computation. -/
theorem pi_upper_finite_96098_3300000 (n : ℕ) (h1 : 96098 ≤ n) (h2 : n < 3300000) :
    (Nat.primeCounting n : ℝ) ≤ 1.10555 * n / Real.log n := by
  sorry

/-- PROVED from the leaves: `exp 15 < 3300000`. -/
private theorem exp15_lt : Real.exp 15 < 3300000 := by
  have h : Real.exp 15 = Real.exp 1 ^ 15 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have he := Real.exp_one_lt_d9
  calc Real.exp 1 ^ 15 < (2.7182818286 : ℝ) ^ 15 :=
        pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
    _ < 3300000 := by norm_num

/-- PROVED from the leaves, with exactly the statement `ChebyshevBoundsFrom 96098` unfolded. -/
theorem chebyshev_pi_bounds_from_96098_of_leaves :
    ∀ n : ℕ, 96098 ≤ n →
      (0.92129 : ℝ) * n / Real.log n ≤ (Nat.primeCounting n : ℝ) ∧
        (Nat.primeCounting n : ℝ) ≤ 1.10555 * n / Real.log n := by
  intro n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hn0 : (0 : ℝ) < n := by linarith
  constructor
  · have h := rs_pi_gt_div_log n (by omega)
    have h2 : (0.92129 : ℝ) * n / Real.log n ≤ (n : ℝ) / Real.log n := by
      apply div_le_div_of_nonneg_right _ hlog.le
      nlinarith
    linarith
  · by_cases hs : n < 3300000
    · exact pi_upper_finite_96098_3300000 n hn hs
    · have hbig : (3300000 : ℝ) ≤ n := by exact_mod_cast (by omega : 3300000 ≤ n)
      have h15 : 15 ≤ Real.log n := by
        rw [Real.le_log_iff_exp_le hn0]
        linarith [exp15_lt]
      have h := rs_pi_lt_div_log_mul n (by omega)
      have hq : 3 / (2 * Real.log n) ≤ 1 / 10 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have hd : 0 ≤ (n : ℝ) / Real.log n := by positivity
      have h3 : (n : ℝ) / Real.log n * (1 + 3 / (2 * Real.log n)) ≤ 1.10555 * n / Real.log n := by
        rw [mul_div_assoc]
        have : (1 + 3 / (2 * Real.log n)) ≤ 1.10555 := by linarith
        nlinarith
      linarith

end LeanLab.ChebyshevExplicit.Novelty1615

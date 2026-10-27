/-
Kaniecki 1995, P0022: certified bounds for `exp`, `log`, `π` used to check the paper's constants.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
All bounds come from Mathlib's Taylor remainder `Real.exp_bound` and the nine digit bounds on `e`.
-/
import Mathlib

namespace LeanLab.Kaniecki1995
open Real Finset

/-- Taylor upper bound for `exp` on `[-1, 1]`. -/
theorem exp_le_taylor {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    exp x ≤ (∑ m ∈ range n, x ^ m / m.factorial) + |x| ^ n * ((n.succ : ℝ) / (n.factorial * n)) := by
  have h := Real.exp_bound hx hn
  have := (abs_sub_le_iff.1 h).1
  linarith

/-- Taylor lower bound for `exp` on `[-1, 1]`. -/
theorem taylor_le_exp {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    (∑ m ∈ range n, x ^ m / m.factorial) - |x| ^ n * ((n.succ : ℝ) / (n.factorial * n)) ≤ exp x := by
  have h := Real.exp_bound hx hn
  have := (abs_sub_le_iff.1 h).2
  linarith

/-- `exp n ≤ 2.7182818286 ^ n`. -/
theorem exp_nat_le (n : ℕ) : exp n ≤ (2.7182818286 : ℝ) ^ n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le n

/-- `2.7182818283 ^ n ≤ exp n`. -/
theorem nat_le_exp (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ exp n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n

/-- Upper bound for `exp (n + r)` from a Taylor bound for `exp r`. -/
theorem exp_add_nat_le {n : ℕ} {r B : ℝ} (hr : |r| ≤ 1)
    (h : (2.7182818286 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) +
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14))) ≤ B) :
    exp ((n : ℝ) + r) ≤ B := by
  rw [Real.exp_add]
  calc exp n * exp r ≤ (2.7182818286 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) +
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14))) :=
        mul_le_mul (exp_nat_le n) (exp_le_taylor hr 14 (by norm_num)) (exp_pos r).le
          (by positivity)
    _ ≤ B := h

/-- Lower bound for `exp (n + r)` from a Taylor bound for `exp r`. -/
theorem le_exp_add_nat {n : ℕ} {r B : ℝ} (hr : |r| ≤ 1)
    (hpos : 0 ≤ (∑ m ∈ range 14, r ^ m / m.factorial) -
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14)))
    (h : B ≤ (2.7182818283 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) -
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14)))) :
    B ≤ exp ((n : ℝ) + r) := by
  rw [Real.exp_add]
  calc B ≤ _ := h
    _ ≤ exp n * exp r :=
        mul_le_mul (nat_le_exp n) (taylor_le_exp hr 14 (by norm_num)) hpos (exp_pos _).le

/-- Upper bound for `exp (-(n + r))`, `0 ≤ r ≤ 1`. -/
theorem exp_neg_le {n : ℕ} {r B : ℝ} (hr : |r| ≤ 1)
    (hpos : 0 < (∑ m ∈ range 14, r ^ m / m.factorial) -
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14)))
    (h : 1 ≤ B * ((2.7182818283 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) -
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14))))) :
    exp (-((n : ℝ) + r)) ≤ B := by
  rw [Real.exp_neg]
  have hE := le_exp_add_nat (n := n) hr hpos.le le_rfl
  have hp : 0 < (2.7182818283 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) -
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14))) := by positivity
  rw [inv_le_iff_one_le_mul₀ (exp_pos _)]
  calc (1 : ℝ) ≤ B * _ := h
    _ ≤ B * exp ((n : ℝ) + r) := by
        have hB : 0 ≤ B := by
          by_contra hneg; push Not at hneg
          have : B * ((2.7182818283 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) -
            |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14)))) < 0 :=
            mul_neg_of_neg_of_pos hneg hp
          linarith
        exact mul_le_mul_of_nonneg_left hE hB

/-- Lower bound for `exp (-(n + r))`. -/
theorem le_exp_neg {n : ℕ} {r B : ℝ} (hr : |r| ≤ 1) (hB : 0 ≤ B)
    (h : B * ((2.7182818286 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) +
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14)))) ≤ 1) :
    B ≤ exp (-((n : ℝ) + r)) := by
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (exp_pos _)]
  have hE := exp_add_nat_le (n := n) hr le_rfl
  calc B * exp ((n : ℝ) + r) ≤ B * _ := mul_le_mul_of_nonneg_left hE hB
    _ ≤ 1 := h

end LeanLab.Kaniecki1995

#print axioms LeanLab.Kaniecki1995.exp_le_taylor
#print axioms LeanLab.Kaniecki1995.taylor_le_exp
#print axioms LeanLab.Kaniecki1995.exp_nat_le
#print axioms LeanLab.Kaniecki1995.nat_le_exp
#print axioms LeanLab.Kaniecki1995.exp_add_nat_le
#print axioms LeanLab.Kaniecki1995.le_exp_add_nat
#print axioms LeanLab.Kaniecki1995.exp_neg_le
#print axioms LeanLab.Kaniecki1995.le_exp_neg

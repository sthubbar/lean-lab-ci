import Mathlib

/-!
Berndt 1972 pages 153 and 154, components of the positive Laurent bound.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp608a
open MeasureTheory Set
/-- Berndt 1972 page 154 display 3.5 in unsigned Stirling notation. -/
theorem stirlingFirst_mul_factorial_le (n j : ℕ) :
    Nat.stirlingFirst (n + 1) (j + 1) * j.factorial ≤ n.choose j * n.factorial := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp [Nat.stirlingFirst_self]
    | succ j =>
      rw [Nat.stirlingFirst_eq_zero_of_lt (by omega)]
      simp
  | succ n ih =>
    cases j with
    | zero => simp [Nat.stirlingFirst_one_right]
    | succ j =>
      by_cases hj : j ≤ n
      · rw [Nat.stirlingFirst_succ_succ, Nat.factorial_succ, Nat.choose_succ_succ,
          Nat.factorial_succ]
        have h1 := Nat.mul_le_mul_left (n + 1) (ih (j + 1))
        have h2 := Nat.mul_le_mul_right (j + 1) (ih j)
        have h3 := Nat.mul_le_mul_right (n.choose j * n.factorial)
          (show j + 1 ≤ n + 1 by omega)
        simp only [Nat.factorial_succ, Nat.succ_eq_add_one] at h1 h2 h3 ⊢
        nlinarith
      · rw [Nat.stirlingFirst_eq_zero_of_lt (by omega)]
        simp

/-- Berndt 1972 page 154, the termwise inequality after display 3.7. -/
theorem binomial_moment_le (n j : ℕ) (hn : 1 ≤ n) :
    (n.choose j : ℝ) ^ 2 * j.factorial / (n : ℝ) ^ (j + 1) ≤
      (n.choose j : ℝ) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Nat.choose_le_pow_div (α := ℝ) j n
  have hf : (0 : ℝ) < j.factorial := by positivity
  rw [le_div_iff₀ hf] at h
  apply (div_le_div_iff₀ (pow_pos hn' _) hn').2
  rw [pow_succ (n : ℝ) j]
  nlinarith [mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ n.choose j by positivity)]


/-- Berndt 1972 page 154, summing the binomial moments in Theorem 2. -/
theorem binomial_moment_sum_le (n : ℕ) (hn : 1 ≤ n) (C : ℝ) (hC : 0 ≤ C) :
    C / (2 * Real.pi) ^ n *
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) ^ 2 * j.factorial /
        (n : ℝ) ^ (j + 1)) ≤ C / ((n : ℝ) * Real.pi ^ n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) ^ 2 * j.factorial /
      (n : ℝ) ^ (j + 1)) ≤ (2 : ℝ) ^ n / n := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) / n :=
        Finset.sum_le_sum (fun j _ => binomial_moment_le n j hn)
      _ = (2 : ℝ) ^ n / n := by
        rw [← Finset.sum_div]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ C / (2 * Real.pi) ^ n * ((2 : ℝ) ^ n / n) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hC (by positivity))
    _ = C / ((n : ℝ) * Real.pi ^ n) := by
      rw [mul_pow]
      field_simp

/-- Berndt 1972 page 154 display 3.7 has an exceptional odd degree one.
This interior point avoids any convention for the periodic endpoint. -/
theorem bernoulli_one_exceeds_odd_bound :
    2 / (2 * Real.pi) < |bernoulliFun 1 (1 / 8)| / (Nat.factorial 1 : ℝ) := by
  norm_num [bernoulliFun_one]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2
  nlinarith [Real.pi_gt_three]

/-- An elementary majorant for the degree-one derivative in Berndt display 3.1. -/
theorem abs_one_sub_le_quadratic (y : ℝ) (hy : 0 ≤ y) :
    |1 - y| ≤ 1 + y ^ 2 / 8 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (y - 4)]
  · nlinarith [sq_nonneg y]

/-- Berndt 1972 page 154, the coefficient comparison from displays 3.5 and 3.6. -/
theorem stirling_coefficient_le_choose_sq (n j : ℕ) (hj : j ≤ n) :
    (Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial ≤
      (n.choose j : ℝ) ^ 2 := by
  have h := stirlingFirst_mul_factorial_le n (n - j)
  rw [Nat.choose_symm hj] at h
  have hr : (Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) * (n - j).factorial ≤
      (n.choose j : ℝ) * n.factorial := by
    rw [show n + 1 - j = n - j + 1 by omega]
    exact_mod_cast h
  have hf : (n.factorial : ℝ) = (n.choose j : ℝ) * j.factorial * (n - j).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hj).symm
  rw [hf] at hr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < j.factorial)).2
  apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < (n - j).factorial)).mp
  nlinarith only [hr]

end LeanLab.ChirreHagen2025.Decomp608a

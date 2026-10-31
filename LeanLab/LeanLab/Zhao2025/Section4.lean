import Mathlib
import LeanLab.Pintz2018.Section9

/-!
# Zhao 2025, Sections 3 and 4 arithmetic

G. Zhao, "The exceptional set of Goldbach problem and Linnik's constant", arXiv 2511.05631v2.
Theorem 1.2 reduces to `∑ Sᵢ² ≤ 1 - c₁` with `Sᵢ = ∑ e^{-(10/3) λ_{i,j}}`, settled in five cases
in Section 4.  This file proves the arithmetic of those cases from the printed bounds on `T` and
`R` (the zero-density inputs), which enter as hypotheses or as the printed numbers.
AI wrote the Lean code.
-/

namespace LeanLab.Zhao2025

open LeanLab.Pintz2018

/-- The exponent `k` of Lemma 3.1 equals `8/3` at `φ = 1/3, x = 1/12, y = 1/4, z = 1/6`, the
choice behind (3.13). -/
theorem k_313 : 2 * (2 * (1 / 3 : ℝ) + 3 * (1 / 12) + 1 / 4 + 1 / 6) = 8 / 3 := by norm_num

/-- (3.19): `10/3 - k` at `x = 0.029, y = 0.083, z = 0.052` is at least `2.22`. -/
theorem k_319 : (2.22 : ℝ) ≤ 10 / 3 - 2 * (1 / 3 + 3 * 0.029 + 0.083 + 0.052) := by norm_num

/-- (3.16), (3.20): for `Λ ≥ 5.2`, `100 e^{-2.22 Λ} ≤ 0.001`, and the value at `5.2` is below
`0.00097`. -/
theorem cor32 (L : ℝ) (hL : 5.2 ≤ L) : 100 * Real.exp (-2.22 * L) ≤ 0.001 := by
  have h1 := expneg_upper (2.22 * 5.2 / 2) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h2 : Real.exp (-2.22 * L) ≤ Real.exp (-2.22 * 5.2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-2.22 * 5.2) = Real.exp (-(2.22 * 5.2 / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h4 : 0 ≤ Real.exp (-(2.22 * 5.2 / 2)) := (Real.exp_pos _).le
  rw [h3] at h2
  nlinarith

theorem t_320 : 100 * Real.exp (-2.22 * 5.2) < 0.00097 := by
  have h1 := expneg_upper (2.22 * 5.2 / 2) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h3 : Real.exp (-2.22 * 5.2) = Real.exp (-(2.22 * 5.2 / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h4 : 0 ≤ Real.exp (-(2.22 * 5.2 / 2)) := (Real.exp_pos _).le
  rw [h3]
  nlinarith

/-! ### `exp (-y) ≤ 1 - y + y²/2` -/

theorem exp_neg_le_quad (y : ℝ) (h0 : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have hs := Real.sum_le_exp_of_nonneg h0 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hs
  norm_num at hs
  have hp : 0 < 1 + y + y ^ 2 / 2 := by positivity
  rw [Real.exp_neg]
  have h1 : (Real.exp y)⁻¹ ≤ (1 + y + y ^ 2 / 2)⁻¹ := inv_anti₀ hp (by linarith)
  have h2 : (1 + y + y ^ 2 / 2)⁻¹ ≤ 1 - y + y ^ 2 / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    nlinarith [pow_two_nonneg (y ^ 2)]
  linarith

/-! ### The case `λ_{1,1} ∈ [c₀, 0.01]`, (4.1) to (4.6) -/

/-- (4.5) and (4.6): if `Λ ≥ 0` and `e^{-Λ/1.09} ≤ λ` (that is `Λ ≥ 1.09 log (1/λ)`) with
`0 < λ ≤ 0.01`, then `e^{-(20/3) λ} + 202 e^{-2.22 Λ} ≤ 1 - 4 λ`.  So `c₁ = 4 c₀` works. -/
theorem case1_bound (l L : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 0.01) (hL : 0 ≤ L)
    (hu : Real.exp (-(L / 1.09)) ≤ l) :
    Real.exp (-(20 / 3) * l) + 202 * Real.exp (-2.22 * L) ≤ 1 - 4 * l := by
  have h1 : Real.exp (-(20 / 3) * l) ≤ 1 - 20 / 3 * l + (20 / 3 * l) ^ 2 / 2 := by
    have := exp_neg_le_quad (20 / 3 * l) (by positivity)
    rwa [show -(20 / 3) * l = -(20 / 3 * l) by ring]
  have h2 : Real.exp (-2.22 * L) ≤ Real.exp (-(L / 1.09)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have : L / 1.09 = L * (100 / 109) := by ring
    rw [this]
    nlinarith
  have h3 : 0 ≤ Real.exp (-(L / 1.09)) := (Real.exp_pos _).le
  have h4 : Real.exp (-(L / 1.09)) ^ 2 ≤ l ^ 2 := by nlinarith
  nlinarith

/-- The critical value in (4.5): `e^{-(20/3) λ_c} + 202 e^{-2.22 · 5.68} < 0.9650` where
`λ_c = e^{-5.68/1.09}`. -/
theorem case1_critical :
    Real.exp (-(20 / 3) * Real.exp (-(5.68 / 1.09))) + 202 * Real.exp (-2.22 * 5.68) < 0.9650 := by
  have hl := expneg_lower (5.68 / 1.09) (by norm_num) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hl
  norm_num at hl
  have hl' : 0.005454 ≤ Real.exp (-(5.68 / 1.09)) := by
    norm_num
    linarith
  have h1 : Real.exp (-(20 / 3) * Real.exp (-(5.68 / 1.09)))
      ≤ Real.exp (-(909 / 25000)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 := expneg_upper (20 / 3 * 0.005454) (by norm_num)
  have h3 := expneg_upper (2.22 * 5.68 / 2) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2 h3
  norm_num at h2 h3
  have h4 : Real.exp (-2.22 * 5.68) = Real.exp (-(2.22 * 5.68 / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h5 : 0 ≤ Real.exp (-(2.22 * 5.68 / 2)) := (Real.exp_pos _).le
  rw [h4]
  nlinarith

/-! ### The later cases, printed arithmetic -/

/-- `e^{-(10/3) · 0.3} = e^{-1} ≤ 0.3679`. -/
theorem exp_neg_one_le : Real.exp (-1) ≤ 0.3679 := by
  have h := Real.exp_one_gt_d9
  rw [Real.exp_neg]
  rw [inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
  nlinarith

/-- (4.9). -/
theorem eq49 : (0.3679 + 0.1231 : ℝ) ^ 2 + 0.0971 * 6.85 < 0.90622 := by norm_num

/-- (4.14), with the sum of the `Rᵢ` equal to `0.457` as in (4.13). -/
theorem eq414 : (0.157 : ℝ) * 0.457 + 0.0704 * (2 * 0.457 + 6.33) < 0.58174 := by norm_num

/-- (4.17) and (4.19). -/
theorem eq417 : (2 * (0.374 + 0.0808) ^ 2 : ℝ) < 0.41369 ∧ (0.556 + 0.0808 : ℝ) ^ 2 < 0.40552 := by
  norm_num

/-- (4.20): the case `λ_{1,1} ∈ [0.40, 0.60]` for both `i₀ = 1` and `i₀ = 2`. -/
theorem eq420 :
    (0.157 : ℝ) * 0.457 + 0.0704 * (2 * 0.457 + 6.33) + 2 * (0.374 + 0.0808) ^ 2 < 0.9955 ∧
    (0.157 : ℝ) * 0.457 + 0.0704 * (2 * 0.457 + 6.33) + (0.556 + 0.0808) ^ 2 < 0.9955 := by
  norm_num

/-- (4.24), the case `λ_{1,1} ∈ [0.60, 0.62]`. -/
theorem eq424 :
    (0.3 : ℝ) * 0.581 + 0.0927 * (2 * 0.581 + 7.63)
      + 2 * (0.1001 - 0.0927) * (2 * 0.3 + 0.1001) < 0.99968 ∧
    (0.9996 : ℝ) < 0.3 * 0.581 + 0.0927 * (2 * 0.581 + 7.63)
      + 2 * (0.1001 - 0.0927) * (2 * 0.3 + 0.1001) := by
  norm_num

/-- The printed (4.14) with `0.557` in place of `0.457` does not give the printed `0.5817`. -/
theorem eq414_as_printed : (0.157 : ℝ) * 0.557 + 0.0704 * (2 * 0.457 + 6.33) > 0.597 := by
  norm_num

/-- Every case closes strictly below 1. -/
theorem all_cases_lt_one :
    (0.965 : ℝ) < 1 ∧ (0.9065 : ℝ) < 1 ∧ (0.9955 : ℝ) < 1 ∧ (0.99968 : ℝ) < 1 := by norm_num

end LeanLab.Zhao2025

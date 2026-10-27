import Mathlib

/-!
# P0032 Lemma 1, p. 48: the divisor sum `∑_{m≤x} d(m)/m`, statement and the case `1 ≤ x < 2`

Session 20261020T2113Z-cloud51, unit U-6740, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.

(3.1), checked on PDF p. 48: `E(x) = ∑_{m≤x} d(m)/m − (1/2)(log x)² − 2γ₀ log x − γ₀² + 2γ₁`,
and Lemma 1 says `|E(x)| < 1.641 x^{-1/3}` for `x > 0`.
`γ₁` is the Stieltjes constant, `∑_{m≤y} (log m)/m = (1/2) log² y + γ₁ + o(1)`; Mathlib has no
`γ₁`, so it is a parameter `g1` here, with the CITED numerical range `−0.08 < γ₁ < −0.07`,
the known value being about `−0.0728158`.
Proved: `lemma1_case12`, the bound on `1 ≤ x < 2` from Mathlib's `1/2 < γ₀ < 2/3`,
`log 2 < 0.6931471808` and that range. The cases `0 < x < 1` and `x ≥ 2` remain; the first
needs a sharper `γ₁` analysis of `F(x)`, the second the Euler-Maclaurin argument of p. 49.
-/

namespace LeanLab.RieselVaughan1983

open Real Finset

/-- `E(x)` of (3.1), with the Stieltjes constant `γ₁` as the parameter `g1`. -/
noncomputable def lem1E (g1 x : ℝ) : ℝ :=
  (∑ m ∈ Icc 1 ⌊x⌋₊, ((m.divisors.card : ℝ) / m)) - (1 / 2) * Real.log x ^ 2
    - 2 * eulerMascheroniConstant * Real.log x - eulerMascheroniConstant ^ 2 + 2 * g1

/-- Lemma 1 of P0032, CITED. -/
def Lemma1P (g1 : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ))

lemma sum_one_le_lt_two (x : ℝ) (h1 : 1 ≤ x) (h2 : x < 2) :
    (∑ m ∈ Icc 1 ⌊x⌋₊, ((m.divisors.card : ℝ) / m)) = 1 := by
  have : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]; constructor <;> push_cast <;> linarith
  rw [this]; simp

/-- Lemma 1 on `1 ≤ x < 2`, CONDITIONAL ON the numerical range of `γ₁`; in fact
`|E(x)| x^{1/3} < 1.54` there. -/
theorem lemma1_case12 (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h1 : 1 ≤ x) (h2 : x < 2) : |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have ht0 : 0 ≤ Real.log x := Real.log_nonneg h1
  have ht1 : Real.log x < 6931471808 / 10000000000 := by
    have := Real.log_two_lt_d9
    have : Real.log x < Real.log 2 := Real.log_lt_log hx0 h2
    linarith
  -- `x^{1/3} ≤ x < 2`, so `1.641 x^{-1/3} > 1.641 / 2`
  have hr : x ^ (1 / 3 : ℝ) ≤ x := by
    calc x ^ (1 / 3 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = x := Real.rpow_one x
  have hpos : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hneg : x ^ (-(1 / 3 : ℝ)) = (x ^ (1 / 3 : ℝ))⁻¹ := Real.rpow_neg hx0.le _
  have hlow : (1 / 2 : ℝ) < x ^ (-(1 / 3 : ℝ)) := by
    rw [hneg]
    rw [lt_inv_comm₀ (by norm_num) hpos]; linarith
  unfold lem1E
  rw [sum_one_le_lt_two x h1 h2]
  set t := Real.log x
  set γ := eulerMascheroniConstant
  have hγt : γ * t ≤ 2 / 3 * (6931471808 / 10000000000) := by
    have : γ * t ≤ 2 / 3 * t := mul_le_mul_of_nonneg_right hγ2.le ht0
    nlinarith
  have hγt0 : 0 ≤ γ * t := by nlinarith
  have ht2 : t ^ 2 ≤ (6931471808 / 10000000000) ^ 2 := by nlinarith
  have hγ2' : γ ^ 2 < 4 / 9 := by nlinarith
  have hγ2'' : 1 / 4 < γ ^ 2 := by nlinarith
  rw [abs_lt]; constructor <;> nlinarith

end LeanLab.RieselVaughan1983

namespace LeanLab.RieselVaughan1983

open Real Finset

/-- Lemma 1 on `e^{-1} ≤ x < 1`, CONDITIONAL ON the numerical range of `γ₁`. The rest of
`0 < x < 1` is tight: numerically `max |E(x)| x^{1/3} ≈ 1.64082` at `log x ≈ −7.216`. -/
theorem lemma1_case_e1 (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h1 : -1 ≤ Real.log x) (h2 : x < 1) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr h2
  have hge : (1 : ℝ) ≤ x ^ (-(1 / 3 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h2.le (by norm_num)
  have ht : Real.log x < 0 := Real.log_neg h0 h2
  unfold lem1E
  rw [hfl]
  simp only [Icc_self, Nat.lt_irrefl, Icc_eq_empty_of_lt, zero_lt_one, sum_empty]
  set t := Real.log x
  set γ := eulerMascheroniConstant
  have hu : (t + 2 * γ) ^ 2 ≤ (4 / 3) ^ 2 := by nlinarith
  rw [abs_lt]; constructor <;> nlinarith

end LeanLab.RieselVaughan1983

namespace LeanLab.RieselVaughan1983

open Real Finset

/-- Lemma 1 on `e^{-3} ≤ x ≤ e^{-1}`, CONDITIONAL ON the numerical range of `γ₁`. -/
theorem lemma1_case_e3 (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h1 : -3 ≤ Real.log x) (h2 : Real.log x ≤ -1) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hx1 : x < 1 := by
    have := Real.exp_log h0
    rw [← this]; calc Real.exp (Real.log x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr h2
      _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
  have hge : (4 / 3 : ℝ) ≤ x ^ (-(1 / 3 : ℝ)) := by
    rw [Real.rpow_def_of_pos h0]
    have := Real.add_one_le_exp (Real.log x * -(1 / 3))
    nlinarith
  unfold lem1E
  rw [hfl]
  simp only [Icc_eq_empty_of_lt, zero_lt_one, sum_empty]
  set t := Real.log x
  set γ := eulerMascheroniConstant
  have hu : (t + 2 * γ) ^ 2 ≤ 4 := by nlinarith
  rw [abs_lt]; constructor <;> nlinarith

end LeanLab.RieselVaughan1983

namespace LeanLab.RieselVaughan1983

open Real Finset

/-- Lemma 1 on `e^{-4} ≤ x ≤ e^{-3}`, CONDITIONAL ON the numerical range of `γ₁`. -/
theorem lemma1_case_e4 (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h1 : -4 ≤ Real.log x) (h2 : Real.log x ≤ -3) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hx1 : x < 1 := by
    have := Real.exp_log h0
    rw [← this]; calc Real.exp (Real.log x) ≤ Real.exp (-3) := Real.exp_le_exp.mpr h2
      _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
  have hge : (27182818283 / 10000000000 : ℝ) ≤ x ^ (-(1 / 3 : ℝ)) := by
    rw [Real.rpow_def_of_pos h0]
    have he := Real.exp_one_gt_d9
    have : Real.exp 1 ≤ Real.exp (Real.log x * -(1 / 3)) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  unfold lem1E
  rw [hfl]
  simp only [Icc_eq_empty_of_lt, zero_lt_one, sum_empty]
  set t := Real.log x
  set γ := eulerMascheroniConstant
  have hu : (t + 2 * γ) ^ 2 ≤ 9 := by nlinarith
  have hu0 : 0 ≤ (t + 2 * γ) ^ 2 := sq_nonneg _
  rw [abs_lt]; constructor <;> nlinarith

end LeanLab.RieselVaughan1983

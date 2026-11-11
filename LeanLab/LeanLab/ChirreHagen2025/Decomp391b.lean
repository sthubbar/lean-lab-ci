import LeanLab.ChirreHagen2025.Decomp391a
import LeanLab.ChirreHagen2025.IntegralRepair391c

/-!
Alternative supply for Decomp358d.mangoldt_large_range.
Use Ramare page 119 up to the unevaluated auxiliary integral and the
proved conservative scalar bound instead of the audited page 120 step.
JRT page 4 Lemma 10 retains its exact 0.67 conclusion.
https://doi.org/10.4064/aa159-2-2
https://arxiv.org/abs/2303.13785
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp391b
open ArithmeticFunction MeasureTheory Set

/-- Ramare page 119, retain the auxiliary integral before the audited comparison. -/
noncomputable def correctedTail (x : ℝ) : ℝ :=
  if Real.log x < 2 * 5.69693 * Real.log (2.44 * 10 ^ 12) ^ 2 then 1.75 / 10 ^ 12
  else ∫ u in Ioi (Real.log (2.44 * 10 ^ 12 : ℝ)),
    u * Real.exp (-(Real.log x / 5.69693) / u - u) / (2 * Real.pi)

/-- Ramare pages 118 and 119, the transition parameter covers the scalar repair. -/
theorem transition_parameter (x : ℝ)
    (hx : 2 * 5.69693 * Real.log (2.44 * 10 ^ 12) ^ 2 ≤ Real.log x) :
    1568 ≤ Real.log x / 5.69693 := by
  have hl : 28 ≤ Real.log (2.44 * 10 ^ 12 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    calc
      Real.exp 28 = Real.exp 1 ^ (28 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.72 : ℝ) ^ 28 := by gcongr; linarith [Real.exp_one_lt_d9]
      _ ≤ 2.44 * 10 ^ 12 := by norm_num
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 28) hl 2
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 5.69693)).mpr
  nlinarith

/-- JRT page 4 scalar budget, valid for the retained auxiliary integral. -/
theorem corrected_tail_scaled (x : ℝ) (hx : 100000 ≤ x) :
    correctedTail x * Real.log x ^ 2 ≤ 1 / 1000 := by
  unfold correctedTail
  split_ifs with hsmall
  · have hh := Decomp429e.zero_tail_scaled_bound x hx
    simpa only [Decomp429e.zeroTailError, if_pos hsmall] using hh
  · have ht : 0 < Real.log (2.44 * 10 ^ 12 : ℝ) := Real.log_pos (by norm_num)
    have hh := IntegralRepair391c.auxiliary_integral_scaled
      (Real.log x / 5.69693) _ (transition_parameter x (le_of_not_gt hsmall)) ht
    have heq : (5.69693 : ℝ) * (Real.log x / 5.69693) = Real.log x := by ring
    simpa only [heq] using hh

/-- JRT page 4 budget generalized to any error with the proved scaled allowance. -/
theorem transfer_budget_of_scaled_error (x E : ℝ) (hx : 100000 ≤ x)
    (hE : E * Real.log x ^ 2 ≤ 1 / 1000) :
    (if x ≤ 10 ^ 19 then 0.94 / Real.sqrt x else 0.64673 / Real.log x ^ 2) +
      0.047 / Real.sqrt x + (Real.log (2 * Real.pi) + 0.0001) / x +
        E ≤ 0.67 / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs : 300 ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  have hr := Decomp429e.log_square_sqrt_bounds x hx
  have hself : Real.log x ^ 2 / x ≤ 1 / 600 := by
    have heq : Real.log x ^ 2 / x = (Real.log x ^ 2 / Real.sqrt x) / Real.sqrt x := by
      rw [div_div, ← pow_two, Real.sq_sqrt hx0.le]
    rw [heq]
    apply (div_le_iff₀ hs0).mpr
    nlinarith [hr.1]
  have hlogpi : Real.log (2 * Real.pi) ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he : (8 : ℝ) ≤ Real.exp 3 := by
      calc
        (8 : ℝ) ≤ (2.7 : ℝ) ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := by gcongr; linarith [Real.exp_one_gt_d9]
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    linarith [Real.pi_lt_four]
  have hc : ((Real.log (2 * Real.pi) + 0.0001) / x) * Real.log x ^ 2 ≤
      3.0001 / 600 := by
    calc
      _ = (Real.log (2 * Real.pi) + 0.0001) * (Real.log x ^ 2 / x) := by ring
      _ ≤ 3.0001 * (Real.log x ^ 2 / x) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := by nlinarith [hself]
  have ht (C : ℝ) (hC : Real.log x ^ 2 / Real.sqrt x ≤ C) :
      (0.047 / Real.sqrt x) * Real.log x ^ 2 ≤ 0.047 * C := by
    calc
      _ = 0.047 * (Real.log x ^ 2 / Real.sqrt x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hC (by norm_num)
  have he := hE
  apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
  by_cases hsmall : x ≤ (10 ^ 19 : ℝ)
  · rw [if_pos hsmall]
    have hm : (0.94 / Real.sqrt x) * Real.log x ^ 2 ≤ 0.47 := by
      calc
        _ = 0.94 * (Real.log x ^ 2 / Real.sqrt x) := by ring
        _ ≤ 0.94 * (1 / 2) := mul_le_mul_of_nonneg_left hr.1 (by norm_num)
        _ = _ := by norm_num
    have hh := ht (1 / 2) hr.1
    nlinarith
  · rw [if_neg hsmall]
    have hh := ht (1 / 100) (hr.2 (lt_of_not_ge hsmall).le)
    have hm : (0.64673 / Real.log x ^ 2) * Real.log x ^ 2 = 0.64673 := by field_simp
    nlinarith


/-- LEAF. Ramare page 118 equation 5.1 and page 119 last upper bound on J.
This isolates the zero input before the audited scalar integration on page 120.
It contains neither a Mangoldt sum nor a psi estimate. -/
theorem zero_sum_reduction (x : ℝ) (hx : 100000 ≤ x) :
    ‖∑' ρ, Decomp391a.zeroTerm x ρ‖ ≤ 0.047 / Real.sqrt x + correctedTail x := by
  sorry

/-- JRT page 3 Lemma 9, using the corrected scalar route.
CONDITIONAL ON the explicit formula and the zero sum reduction. -/
theorem mangoldt_psi_transfer (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) - Real.log x +
        Real.eulerMascheroniConstant ≤
      |Chebyshev.psi x - x| / x + 0.047 / Real.sqrt x +
        (Real.log (2 * Real.pi) + 0.0001) / x + correctedTail x := by
  have hx0 : 0 < x := by linarith
  have hpsi := div_le_div_of_nonneg_right (le_abs_self (Chebyshev.psi x - x)) hx0.le
  have hz := Complex.re_le_norm (-(∑' ρ, Decomp391a.zeroTerm x ρ))
  simp only [Complex.neg_re, norm_neg] at hz
  have hb := zero_sum_reduction x hx
  have hi := Decomp391a.remainder_integral_le x (by linarith)
  rw [(Decomp391a.weighted_explicit_formula x hx).2]
  have hc : Real.log (2 * Real.pi) / x ≤ (Real.log (2 * Real.pi) + 0.0001) / x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith
  linarith

/-- Exact sealed Decomp358d large-range statement through the conservative repair.
CONDITIONAL ON the explicit formula, zero reduction and two existing psi leaves. -/
theorem mangoldt_large_range (m : ℕ) (hm : 100000 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m, vonMangoldt n / (n : ℝ)) ≤
      Real.log (m : ℝ) - Real.eulerMascheroniConstant +
        0.67 / Real.log (m : ℝ) ^ 2 := by
  have hm' : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hpsi : |Chebyshev.psi m - (m : ℝ)| / (m : ℝ) ≤
      if (m : ℝ) ≤ 10 ^ 19 then 0.94 / Real.sqrt m else 0.64673 / Real.log (m : ℝ) ^ 2 := by
    split_ifs with hsmall
    · have hp := Decomp429e.psi_finite_range m hm' hsmall
      have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
      calc
        _ ≤ (0.94 * Real.sqrt m) / (m : ℝ) :=
          div_le_div_of_nonneg_right hp hm0.le
        _ = _ := by
          field_simp
          nlinarith [Real.sq_sqrt hm0.le]
    · have hp := Decomp429e.psi_logarithmic_error m hm'
      have hh := div_le_div_of_nonneg_right hp hm0.le
      convert hh using 1 <;> field_simp
  have htransfer := mangoldt_psi_transfer m hm'
  simp only [Nat.floor_natCast] at htransfer
  have hbudget := transfer_budget_of_scaled_error m (correctedTail m) hm' (corrected_tail_scaled m hm')
  linarith

end LeanLab.ChirreHagen2025.Decomp391b

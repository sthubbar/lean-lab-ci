import LeanLab.ChirreHagen2025.Decomp391aLocal
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


/-- Elementary exponential bound used in the large-tail comparison. -/
lemma exp_neg_half_ge_half : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
  have hepos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    calc
      Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by ring
      _ = Real.exp ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by rw [Real.exp_add]
      _ = Real.exp 1 := by norm_num
  have hone : Real.exp 1 ≤ 4 := by
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hle : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    nlinarith [hsq, hone, sq_nonneg (Real.exp (1 / 2 : ℝ) - 2)]
  have hhalf : (1 / 2 : ℝ) ≤ 1 / Real.exp (1 / 2 : ℝ) := by
    apply (le_div_iff₀ hepos).mpr
    nlinarith
  simpa only [Real.exp_neg, one_div] using hhalf

/-- The repaired auxiliary integral dominates the printed Ramare tail envelope. -/
lemma zero_tail_error_le_correctedTail (x : ℝ) :
    Decomp429e.zeroTailError x ≤ correctedTail x := by
  by_cases hs : Real.log x < 2 * 5.69693 * Real.log (2.44 * 10 ^ 12) ^ 2
  · simp [Decomp429e.zeroTailError, correctedTail, hs]
  · simp only [Decomp429e.zeroTailError, correctedTail, if_neg hs]
    let t : ℝ := Real.log (2.44 * 10 ^ 12 : ℝ)
    let a : ℝ := Real.log x / 5.69693
    let v : ℝ := Real.sqrt a
    have ht0 : 0 < t := by
      dsimp [t]
      exact Real.log_pos (by norm_num)
    have htlo : 28 ≤ t := by
      dsimp [t]
      rw [Real.le_log_iff_exp_le (by norm_num)]
      calc
        Real.exp 28 = Real.exp 1 ^ (28 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ (2.72 : ℝ) ^ 28 := by gcongr; linarith [Real.exp_one_lt_d9]
        _ ≤ 2.44 * 10 ^ 12 := by norm_num
    have hthi : t ≤ 30 := by
      dsimp [t]
      rw [Real.log_le_iff_le_exp (by norm_num)]
      calc
        (2.44 * 10 ^ 12 : ℝ) ≤ (2.7 : ℝ) ^ 30 := by norm_num
        _ ≤ Real.exp 1 ^ 30 := by gcongr; linarith [Real.exp_one_gt_d9]
        _ = Real.exp 30 := by rw [← Real.exp_nat_mul]; norm_num
    have htrans : 2 * 5.69693 * t ^ 2 ≤ Real.log x := by
      simpa [t] using le_of_not_gt hs
    have hl0 : 0 ≤ Real.log x := by
      nlinarith [sq_nonneg t, htrans]
    have ha0 : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg hl0 (by norm_num)
    have h2t2 : 2 * t ^ 2 ≤ a := by
      dsimp [a]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 5.69693)).mpr
      nlinarith
    have hv0 : 0 ≤ v := by
      dsimp [v]
      exact Real.sqrt_nonneg _
    have hv2 : v ^ 2 = a := by
      dsimp [v]
      exact Real.sq_sqrt ha0
    have hv39 : 39 ≤ v := by
      nlinarith
    have hsubset : Icc (v - 4) (v + 4) ⊆ Ioi t := by
      intro u hu
      have hu1 := hu.1
      have hu2 := hu.2
      change t < u
      linarith
    have hi := (IntegralRepair391c.auxiliary_integral_bound a t ha0 ht0).1
    have hpoint (u : ℝ) (hu : u ∈ Icc (v - 4) (v + 4)) :
        (v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi) ≤
          u * Real.exp (-a / u - u) / (2 * Real.pi) := by
      have hu0 : 0 < u := by linarith [hu.1, hv39]
      have hu32 : (32 : ℝ) ≤ u := by linarith [hu.1, hv39]
      have hd2 : (u - v) ^ 2 ≤ 16 := by nlinarith [hu.1, hu.2]
      have hfrac : (u - v) ^ 2 / u ≤ 1 / 2 := by
        apply (div_le_iff₀ hu0).mpr
        nlinarith
      have hident : a / u + u = 2 * v + (u - v) ^ 2 / u := by
        rw [← hv2]
        field_simp
        ring
      have hfrac' : (u - v) ^ 2 ≤ u / 2 := by
        have hh := (div_le_iff₀ hu0).mp hfrac
        nlinarith
      have hbound' : a + u ^ 2 ≤ (2 * v + 1 / 2) * u := by
        rw [← hv2]
        nlinarith [hfrac']
      have hbound : a / u + u ≤ 2 * v + 1 / 2 := by
        calc
          a / u + u = (a + u ^ 2) / u := by field_simp
          _ ≤ (2 * v + 1 / 2) * u / u := by
            gcongr
          _ = 2 * v + 1 / 2 := by field_simp
      have hexp : Real.exp (-(2 * v + 1 / 2)) ≤ Real.exp (-a / u - u) := by
        apply Real.exp_le_exp.mpr
        have harg : -(2 * v + 1 / 2) ≤ -(a / u + u) := by linarith [hbound]
        simpa only [neg_div] using harg
      have hv4 : 0 ≤ v - 4 := by nlinarith [hv39]
      have hvu : v - 4 ≤ u := by linarith [hu.1]
      have hcoeff : (v - 4) * Real.exp (-(2 * v + 1 / 2)) ≤
          u * Real.exp (-(2 * v + 1 / 2)) :=
        mul_le_mul_of_nonneg_right hvu (Real.exp_pos _).le
      have hmain : u * Real.exp (-(2 * v + 1 / 2)) ≤
          u * Real.exp (-a / u - u) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hexp hu0.le
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2
      exact hcoeff.trans hmain
    have hsmall : (∫ u in Icc (v - 4) (v + 4),
          (v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) ≤
        ∫ u in Icc (v - 4) (v + 4),
          u * Real.exp (-a / u - u) / (2 * Real.pi) := by
      apply integral_mono_ae (continuousOn_const.integrableOn_Icc) (hi.mono_set hsubset)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact hpoint u hu
    have hlarge : (∫ u in Icc (v - 4) (v + 4),
          u * Real.exp (-a / u - u) / (2 * Real.pi)) ≤
        ∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi) := by
      apply setIntegral_mono_set hi _ (Filter.Eventually.of_forall hsubset)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := ht0.trans hu
      positivity
    have hconst : (∫ u in Icc (v - 4) (v + 4),
          (v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) =
        8 * ((v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const]
      ring
    have hcore : 8 * (v - 4) * Real.exp (-(1 / 2 : ℝ)) ≥ 1 + 2 * v := by
      have hv4 : 0 ≤ v - 4 := by nlinarith [hv39]
      have hm : (v - 4) * Real.exp (-(1 / 2 : ℝ)) ≥ (v - 4) / 2 := by
        have hh := mul_le_mul_of_nonneg_left exp_neg_half_ge_half hv4
        nlinarith
      calc
        8 * (v - 4) * Real.exp (-(1 / 2 : ℝ)) = 8 * ((v - 4) * Real.exp (-(1 / 2 : ℝ))) := by ring
        _ ≥ 8 * ((v - 4) / 2) := by
          exact mul_le_mul_of_nonneg_left hm (by norm_num)
        _ = 4 * (v - 4) := by ring
        _ ≥ 1 + 2 * v := by nlinarith [hv39]
    have headd : Real.exp (-(2 * v + 1 / 2)) =
          Real.exp (-2 * v) * Real.exp (-(1 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hprod : (1 + 2 * v) * Real.exp (-2 * v) ≤
        8 * ((v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) * (2 * Real.pi) := by
      calc
        (1 + 2 * v) * Real.exp (-2 * v) ≤
            (8 * (v - 4) * Real.exp (-(1 / 2 : ℝ))) * Real.exp (-2 * v) :=
          mul_le_mul_of_nonneg_right hcore (Real.exp_pos _).le
        _ = 8 * ((v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) * (2 * Real.pi) := by
          rw [headd]
          field_simp
          ring
    have hint : 8 * ((v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) ≤
        ∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi) := by
      calc
        8 * ((v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) =
            (∫ u in Icc (v - 4) (v + 4),
              (v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) := by
              exact hconst.symm
        _ ≤ ∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi) :=
          hsmall.trans hlarge
    have hold : (1 + 2 * v) / (2 * Real.pi) * Real.exp (-2 * v) ≤
        ∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi) := by
      rw [show (1 + 2 * v) / (2 * Real.pi) * Real.exp (-2 * v) =
          (1 + 2 * v) * Real.exp (-2 * v) / (2 * Real.pi) by ring]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      calc
        (1 + 2 * v) * Real.exp (-2 * v) ≤
            8 * ((v - 4) * Real.exp (-(2 * v + 1 / 2)) / (2 * Real.pi)) * (2 * Real.pi) := hprod
        _ ≤ (∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi)) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hint (by positivity)
    change (1 + 2 * Real.sqrt a) / (2 * Real.pi) * Real.exp (-2 * Real.sqrt a) ≤
      ∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi)
    simpa [a, v] using hold

/-- LEAF. Ramare page 118 equation 5.1 and page 119 last upper bound on J.
This isolates the zero input before the audited scalar integration on page 120.
It contains neither a Mangoldt sum nor a psi estimate. -/
theorem zero_sum_reduction (x : ℝ) (hx : 100000 ≤ x) :
    ‖∑' ρ, Decomp391a.zeroTerm x ρ‖ ≤ 0.047 / Real.sqrt x + correctedTail x := by
  have hz := Decomp391a.zero_sum_bound x hx
  have ht := zero_tail_error_le_correctedTail x
  exact hz.trans (add_le_add_right ht _)

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


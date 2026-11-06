import LeanLab.ChirreHagen2025.Audit429

/-!
P0075 page 3 and Johnston, Ramare and Trudgian 2023 Lemma 10 page 4.
The transfer uses the written proof in Ramare 2013 pages 118 to 120 and
Chirre, Hagen and Simonic 2024 page 4 equation 3.3 and Remark 7.
https://doi.org/10.4064/aa159-2-2
https://arxiv.org/abs/2303.13785
https://arxiv.org/abs/2206.00819
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429e
open ArithmeticFunction

/-- Ramare 2013 pages 119 and 120, the zero-sum error after its low zeros.
The transition is on log x, as in that written proof, not on x. -/
noncomputable def zeroTailError (x : ℝ) : ℝ :=
  if Real.log x < 2 * 5.69693 * Real.log (2.44 * 10 ^ 12) ^ 2 then 1.75 / 10 ^ 12
  else (1 + 2 * Real.sqrt (Real.log x / 5.69693)) / (2 * Real.pi) *
    Real.exp (-2 * Real.sqrt (Real.log x / 5.69693))

/-- JRT page 4 scalar comparison, obtained from Mathlib logarithmic monotonicity. -/
theorem log_square_sqrt_antitone :
    AntitoneOn (fun x : ℝ => Real.log x ^ 2 / Real.sqrt x) (Set.Ici (Real.exp 4)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := (Real.exp_pos 4).trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 4)).trans hx
  have hy1 : 1 ≤ y := hx1.trans hxy
  have hr := Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 1 / 4)
    (by simpa using hx) (by simpa using hy) hxy
  have hs := pow_le_pow_left₀ (div_nonneg (Real.log_nonneg hy1) (Real.rpow_pos_of_pos hy0 _).le) hr 2
  have hpow (z : ℝ) (hz : 0 < z) : (z ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    norm_num [Real.sqrt_eq_rpow]
  simpa only [div_pow, hpow x hx0, hpow y hy0] using hs

/-- JRT page 4 scalar comparison, two convenient coarse logarithmic envelopes. -/
theorem log_square_sqrt_bounds (x : ℝ) (hx : 100000 ≤ x) :
    Real.log x ^ 2 / Real.sqrt x ≤ 1 / 2 ∧
    ((10 ^ 19 : ℝ) ≤ x → Real.log x ^ 2 / Real.sqrt x ≤ 1 / 100) := by
  have he4 : Real.exp 4 ≤ (100000 : ℝ) := by
    calc
      Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3 : ℝ) ^ 4 := by gcongr; linarith [Real.exp_one_lt_d9]
      _ ≤ 100000 := by norm_num
  constructor
  · have hh := log_square_sqrt_antitone he4 (he4.trans hx) hx
    have hl := Audit429.cutoff_log_bounds
    have hs : (300 : ℝ) ≤ Real.sqrt 100000 := by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
      norm_num
    apply hh.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 100000)).mpr
    nlinarith
  · intro hlarge
    have hb : Real.exp 4 ≤ (10 ^ 19 : ℝ) := he4.trans (by norm_num)
    have hh := log_square_sqrt_antitone hb (hb.trans hlarge) hlarge
    have hl0 : 0 ≤ Real.log (10 ^ 19 : ℝ) := Real.log_nonneg (by norm_num)
    have hl : Real.log (10 ^ 19 : ℝ) ≤ 45 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      calc
        (10 ^ 19 : ℝ) ≤ (2.7 : ℝ) ^ 45 := by norm_num
        _ ≤ Real.exp 1 ^ 45 := by gcongr; linarith [Real.exp_one_gt_d9]
        _ = Real.exp 45 := by rw [← Real.exp_nat_mul]; norm_num
    have hs : (1000000 : ℝ) ≤ Real.sqrt (10 ^ 19) := by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
      norm_num
    have hl2 := pow_le_pow_left₀ hl0 hl 2
    apply hh.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt (10 ^ 19))).mpr
    norm_num at hs hl2 ⊢
    linarith

/-- Ramare pages 119 and 120, an elementary scalar envelope for the zero-tail error. -/
theorem zero_tail_scaled_bound (x : ℝ) (hx : 100000 ≤ x) :
    zeroTailError x * Real.log x ^ 2 ≤ 1 / 1000 := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hT0 : 0 ≤ Real.log (2.44 * 10 ^ 12 : ℝ) := Real.log_nonneg (by norm_num)
  have hTlo : 28 ≤ Real.log (2.44 * 10 ^ 12 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    calc
      Real.exp 28 = Real.exp 1 ^ (28 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.72 : ℝ) ^ 28 := by gcongr; linarith [Real.exp_one_lt_d9]
      _ ≤ 2.44 * 10 ^ 12 := by norm_num
  have hThi : Real.log (2.44 * 10 ^ 12 : ℝ) ≤ 30 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc
      (2.44 * 10 ^ 12 : ℝ) ≤ (2.7 : ℝ) ^ 30 := by norm_num
      _ ≤ Real.exp 1 ^ 30 := by gcongr; linarith [Real.exp_one_gt_d9]
      _ = Real.exp 30 := by rw [← Real.exp_nat_mul]; norm_num
  unfold zeroTailError
  split_ifs with hsmall
  · have hsq := pow_le_pow_left₀ hT0 hThi 2
    have hl : Real.log x ≤ 11000 := by nlinarith
    have hlsq := pow_le_pow_left₀ hl0 hl 2
    nlinarith
  · let u := Real.sqrt (Real.log x / 5.69693)
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = Real.log x / 5.69693 := Real.sq_sqrt (by positivity)
    have hL : Real.log x = 5.69693 * u ^ 2 := by rw [hu2]; ring
    have hu : 39 ≤ u := by
      have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 28) hTlo 2
      have hh := le_of_not_gt hsmall
      rw [hL] at hh
      nlinarith
    have hnum : (1 + 2 * u) * Real.log x ^ 2 ≤ 108 * u ^ 5 := by
      have hl2 : Real.log x ^ 2 ≤ 36 * u ^ 4 := by
        rw [hL, mul_pow, ← pow_mul]
        nlinarith [pow_nonneg hu0 4]
      have hh := mul_le_mul (show 1 + 2 * u ≤ 3 * u by linarith) hl2
        (sq_nonneg (Real.log x)) (show 0 ≤ 3 * u by positivity)
      nlinarith
    have hexp : 108 * u ^ 5 ≤ (0.006 : ℝ) * Real.exp (2 * u) := by
      have hs := Real.pow_div_factorial_le_exp (2 * u) (show 0 ≤ 2 * u by positivity) 10
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 39) hu 5
      have hm := mul_le_mul_of_nonneg_right hp (pow_nonneg hu0 5)
      norm_num at hs hp hm
      nlinarith
    change ((1 + 2 * u) / (2 * Real.pi) * Real.exp (-2 * u)) * Real.log x ^ 2 ≤ _
    rw [show -2 * u = -(2 * u) by ring, Real.exp_neg]
    have heq : ((1 + 2 * u) / (2 * Real.pi) * (Real.exp (2 * u))⁻¹) * Real.log x ^ 2 =
        ((1 + 2 * u) * Real.log x ^ 2) / ((2 * Real.pi) * Real.exp (2 * u)) := by ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < (2 * Real.pi) * Real.exp (2 * u))).mpr
    apply hnum.trans
    apply hexp.trans
    have hp : (0.006 : ℝ) ≤ (1 / 1000) * (2 * Real.pi) := by linarith [Real.pi_gt_three]
    nlinarith [Real.exp_pos (2 * u)]

/-- LEAF. JRT page 3 proof of Lemma 9 and Ramare pages 118 to 120.
The corrected explicit formula transfers the psi error to the weighted
Mangoldt sum. The 0.047 term is the verified low-zero contribution.
No quantitative psi estimate is supplied by this leaf. -/
theorem mangoldt_psi_transfer (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) - Real.log x +
        Real.eulerMascheroniConstant ≤
      |Chebyshev.psi x - x| / x + 0.047 / Real.sqrt x +
        (Real.log (2 * Real.pi) + 0.0001) / x + zeroTailError x := by
  sorry

/-- LEAF. JRT page 3 Lemma 7, used in the written Lemma 10 proof on page 4.
The source cites Buthe Theorem 2 for this unconditional finite-range psi
bound. It contains no weighted Mangoldt sum or logarithmic integral. -/
theorem psi_finite_range (x : ℝ) (hx : 100000 ≤ x) (hxtop : x ≤ 10 ^ 19) :
    |Chebyshev.psi x - x| ≤ 0.94 * Real.sqrt x := by
  sorry

/-- LEAF. JRT page 2 Lemma 6, used in the written Lemma 10 proof on page 4.
The source is Broadbent and collaborators Table 15. This is a pure psi
estimate with no weighted Mangoldt sum. -/
theorem psi_logarithmic_error (x : ℝ) (hx : 100000 ≤ x) :
    |Chebyshev.psi x - x| ≤ 0.64673 * x / Real.log x ^ 2 := by
  sorry

/-- JRT page 4 Lemma 10, the scalar budget after its cited inputs.
Use the log transition in Ramare page 119. This has no arithmetic function. -/
theorem transfer_numeric_budget (x : ℝ) (hx : 100000 ≤ x) :
    (if x ≤ 10 ^ 19 then 0.94 / Real.sqrt x else 0.64673 / Real.log x ^ 2) +
      0.047 / Real.sqrt x + (Real.log (2 * Real.pi) + 0.0001) / x +
        zeroTailError x ≤ 0.67 / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs : 300 ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  have hr := log_square_sqrt_bounds x hx
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
  have he := zero_tail_scaled_bound x hx
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

/-- Exact existing Decomp358d.mangoldt_large_range statement.
CONDITIONAL ON the transfer, the two pure psi estimates and the scalar
budget. The source transition was read in Ramare's original written proof. -/
theorem mangoldt_large_range (m : ℕ) (hm : 100000 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m, vonMangoldt n / (n : ℝ)) ≤
      Real.log (m : ℝ) - Real.eulerMascheroniConstant +
        0.67 / Real.log (m : ℝ) ^ 2 := by
  have hm' : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hpsi : |Chebyshev.psi m - (m : ℝ)| / (m : ℝ) ≤
      if (m : ℝ) ≤ 10 ^ 19 then 0.94 / Real.sqrt m else 0.64673 / Real.log (m : ℝ) ^ 2 := by
    split_ifs with hsmall
    · have hp := psi_finite_range m hm' hsmall
      have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
      calc
        _ ≤ (0.94 * Real.sqrt m) / (m : ℝ) :=
          div_le_div_of_nonneg_right hp hm0.le
        _ = _ := by
          field_simp
          nlinarith [Real.sq_sqrt hm0.le]
    · have hp := psi_logarithmic_error m hm'
      have hh := div_le_div_of_nonneg_right hp hm0.le
      convert hh using 1 <;> field_simp
  have htransfer := mangoldt_psi_transfer m hm'
  simp only [Nat.floor_natCast] at htransfer
  have hbudget := transfer_numeric_budget m hm'
  linarith

end LeanLab.ChirreHagen2025.Decomp429e

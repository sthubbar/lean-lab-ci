import LeanLab.HelfgottMajor.Feed1122ZetaBaseTwo

/-!
# Split of `zeta_zero_free_seventeen_half_ten_half` at height `19/2`, burst 20261122 S137

`Feed1122ZetaBaseTwo` leaves the MEDIUM LEAF `zeta_zero_free_seventeen_half_ten_half`: no zero of
`ζ` in the open strip has ordinate in `(17/2, 21/2]`, Helfgott arXiv 1305.2897v4 Section 4.6
page 56 with Platt's verification and the first zero tables of Gram 1903 and Backlund 1914.

Same route as `Feed1122ZetaBaseTwo` with one more Bernoulli term, Edwards 1974 Chapter 6:
`ζ(s) = 1 + 2^(-s) H₃(s) - s(s+1)⋯(s+5)/2 ∫_2^∞ (B₆({u})/360) u^(-s-6) du`,
`H₃(s) = 1/2 + 2/(s-1) + s/24 - s(s+1)(s+2)/5760 + s(s+1)(s+2)(s+3)(s+4)/967680`.

* PROVED `ibp4_two`, `ibp5_two`, `riemannZeta_eq_EM6_two`.
* PROVED `coeff_six_lo`, `coeff_six_hi`, `box_six_two_poly`, `main_six_two_lt`, `prod_six_two_le`.
* PROVED `riemannZeta_ne_zero_seventeen_half_nineteen_half`: no zero with ordinate in `(17/2, 19/2]`.
* LEAF MEDIUM `zeta_zero_free_nineteen_half_ten_half`: no zero with ordinate in `(19/2, 21/2]`.
* PROVED assembly `zeta_zero_free_seventeen_half_ten_half_s137`, exactly the statement of
  `Feed1122ZetaBaseTwo.zeta_zero_free_seventeen_half_ten_half`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoSix
open Complex Set MeasureTheory LeanLab.HelfgottMajor.Feed1122ZetaEM4
  LeanLab.HelfgottMajor.Feed1122ZetaEM6 LeanLab.HelfgottMajor.Feed1122ZetaBaseTwo

/-- step four on `(2, ∞)`: `∫ (B₄/12) x^(-s-4) = (s+4) ∫ (B₅/60) x^(-s-5)`. -/
lemma ibp4_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 +
        (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 4)) =
      (s + 4) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 +
        5 / 3 * (Int.fract x) ^ 3 - 1 / 6 * Int.fract x) / 60 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 5) := by
  have hc : Continuous fun x : ℝ =>
      ((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 + 5 / 3 * (Int.fract x) ^ 3 -
        1 / 6 * Int.fract x) / 60 := by
    have := ContinuousOn.comp_fract''
      (f := fun y : ℝ => (y ^ 5 - 5 / 2 * y ^ 4 + 5 / 3 * y ^ 3 - 1 / 6 * y) / 60)
      (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ =>
      ((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 + 5 / 3 * (Int.fract x) ^ 3 -
        1 / 6 * Int.fract x) / 60)
      (((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 + (Int.fract x) ^ 2 - 1 / 30) / 12) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := ((((hf.pow 5).sub ((hf.pow 4).const_mul (5 / 2))).add
      ((hf.pow 3).const_mul (5 / 3))).sub (hf.const_mul (1 / 6))).div_const 60
    convert this using 1
    simp
    ring
  have h := ibp_gen2 hc hd (by fun_prop) (by fun_prop) abs_B5_le abs_B4_le
    (P0 := 0) (by intro n; simp) (a := -s - 4) (by simp; linarith)
  have e : (-s - 4 - 1) = -s - 5 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- step five on `(2, ∞)`: `∫ (B₅/60) x^(-s-5) = -2^(-s-5)/15120 + (s+5) ∫ (B₆/360) x^(-s-6)`. -/
lemma ibp5_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 +
        5 / 3 * (Int.fract x) ^ 3 - 1 / 6 * Int.fract x) / 60 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 5)) =
      -(1 / 15120 : ℂ) * (2 : ℂ) ^ (-s - 5) + (s + 5) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 +
        5 / 2 * (Int.fract x) ^ 4 - 1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 : ℝ) : ℂ) *
          (x : ℂ) ^ (-s - 6) := by
  have hc : Continuous fun x : ℝ =>
      ((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
        1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 := by
    have := ContinuousOn.comp_fract''
      (f := fun y : ℝ => (y ^ 6 - 3 * y ^ 5 + 5 / 2 * y ^ 4 - 1 / 2 * y ^ 2 + 1 / 42) / 360)
      (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ =>
      ((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
        1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360)
      (((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 + 5 / 3 * (Int.fract x) ^ 3 -
        1 / 6 * Int.fract x) / 60) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := (((((hf.pow 6).sub ((hf.pow 5).const_mul 3)).add
      ((hf.pow 4).const_mul (5 / 2))).sub ((hf.pow 2).const_mul (1 / 2))).add_const
      (1 / 42 : ℝ)).div_const 360
    convert this using 1
    simp
    ring
  have h := ibp_gen2 hc hd (by fun_prop) (by fun_prop) abs_B6_le abs_B5_le
    (P0 := 1 / 15120) (by intro n; simp; norm_num) (a := -s - 5) (by simp; linarith)
  have e : (-s - 5 - 1) = -s - 6 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- Euler Maclaurin from `n = 2` with three Bernoulli terms, Edwards 1974 Chapter 6. -/
theorem riemannZeta_eq_EM6_two {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = 1 + (2 : ℂ) ^ (-s) * (1 / 2 + 2 / (s - 1) + s / 24 -
        s * (s + 1) * (s + 2) / 5760 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680) -
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 2 * ∫ x in Ioi (2 : ℝ),
        ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
          1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 6) := by
  have h4 := ibp4_two hs
  have h5 := ibp5_two hs
  have p5 : (2 : ℂ) ^ (-s - 5) = (2 : ℂ) ^ (-s) / 32 := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero]
    have : (2 : ℂ) ^ (-(5 : ℂ)) = 1 / 32 := by
      rw [Complex.cpow_neg]
      norm_num
    rw [this]
    ring
  rw [p5] at h5
  rw [riemannZeta_eq_EM4_two hs h1, h4, h5]
  ring

set_option maxHeartbeats 4000000 in
/-- Certificate piece on `[289/4, 325/4]`, proved monomial by monomial. -/
lemma coeff_six_lo (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (289 / 4 : ℝ) ≤ x) (hb : x ≤ (325 / 4 : ℝ)) :
    0 < (-x ^ 6 - 367 * x ^ 5 - 107151 * x ^ 4 - 16761109 * x ^ 3 - 1506978868 * x ^ 2 + (11533581176256 / 25) * x - (39151075590144 / 25)) +
      (-18 * x ^ 5 + 648 * x ^ 4 - 2345178 * x ^ 3 - 485468052 * x ^ 2 + 910177688544 * x - (35532666150912 / 25)) * g +
      (-6 * x ^ 5 - 1263 * x ^ 4 + 230344 * x ^ 3 - 15481975 * x ^ 2 + 410414659192 * x - (31379562529344 / 25)) * g ^ 2 +
      (-90 * x ^ 4 + 5160 * x ^ 3 + 7804482 * x ^ 2 + 59354904 * x + 81545563104) * g ^ 3 +
      (-15 * x ^ 4 - 1382 * x ^ 3 + 686546 * x ^ 2 + 94753489 * x + 415242715820) * g ^ 4 +
      (-180 * x ^ 3 + 11592 * x ^ 2 + 8441874 * x + 126785196) * g ^ 5 +
      (-20 * x ^ 3 - 238 * x ^ 2 + 253456 * x + 577075) * g ^ 6 +
      (-180 * x ^ 2 + 10296 * x - 1707786) * g ^ 7 +
      (-15 * x ^ 2 + 453 * x - 95595) * g ^ 8 +
      (-90 * x + 3216) * g ^ 9 +
      (-6 * x + 205) * g ^ 10 +
      (-18) * g ^ 11 +
      (-1) * g ^ 12 := by
  have hx : 0 ≤ x := by linarith
  have u1 : x ^ 1 ≤ (325 / 4 : ℝ) := by
    calc x ^ 1 ≤ (325 / 4 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (289 / 4 : ℝ) ≤ x ^ 1 := by
    calc (289 / 4 : ℝ) = (289 / 4 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (105625 / 16 : ℝ) := by
    calc x ^ 2 ≤ (325 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (83521 / 16 : ℝ) ≤ x ^ 2 := by
    calc (83521 / 16 : ℝ) = (289 / 4 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (34328125 / 64 : ℝ) := by
    calc x ^ 3 ≤ (325 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (24137569 / 64 : ℝ) ≤ x ^ 3 := by
    calc (24137569 / 64 : ℝ) = (289 / 4 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (11156640625 / 256 : ℝ) := by
    calc x ^ 4 ≤ (325 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (6975757441 / 256 : ℝ) ≤ x ^ 4 := by
    calc (6975757441 / 256 : ℝ) = (289 / 4 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (3625908203125 / 1024 : ℝ) := by
    calc x ^ 5 ≤ (325 / 4 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (2015993900449 / 1024 : ℝ) ≤ x ^ 5 := by
    calc (2015993900449 / 1024 : ℝ) = (289 / 4 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (1178420166015625 / 4096 : ℝ) := by
    calc x ^ 6 ≤ (325 / 4 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (582622237229761 / 4096 : ℝ) ≤ x ^ 6 := by
    calc (582622237229761 / 4096 : ℝ) = (289 / 4 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have hc0 : (6570390934740 : ℝ) ≤ -x ^ 6 - 367 * x ^ 5 - 107151 * x ^ 4 - 16761109 * x ^ 3 - 1506978868 * x ^ 2 + (11533581176256 / 25) * x - (39151075590144 / 25) := by linarith
  have hc1 : (59830204952449 : ℝ) ≤ -18 * x ^ 5 + 648 * x ^ 4 - 2345178 * x ^ 3 - 485468052 * x ^ 2 + 910177688544 * x - (35532666150912 / 25) := by linarith
  have t1 : 0 ≤ (-18 * x ^ 5 + 648 * x ^ 4 - 2345178 * x ^ 3 - 485468052 * x ^ 2 + 910177688544 * x - (35532666150912 / 25)) * g := mul_nonneg (by linarith) (by positivity)
  have hc2 : (28305657639553 : ℝ) ≤ -6 * x ^ 5 - 1263 * x ^ 4 + 230344 * x ^ 3 - 15481975 * x ^ 2 + 410414659192 * x - (31379562529344 / 25) := by linarith
  have t2 : 0 ≤ (-6 * x ^ 5 - 1263 * x ^ 4 + 230344 * x ^ 3 - 15481975 * x ^ 2 + 410414659192 * x - (31379562529344 / 25)) * g ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hc3 : (124597673769 : ℝ) ≤ -90 * x ^ 4 + 5160 * x ^ 3 + 7804482 * x ^ 2 + 59354904 * x + 81545563104 := by linarith
  have t3 : 0 ≤ (-90 * x ^ 4 + 5160 * x ^ 3 + 7804482 * x ^ 2 + 59354904 * x + 81545563104) * g ^ 3 := mul_nonneg (by linarith) (by positivity)
  have hc4 : (424277486068 : ℝ) ≤ -15 * x ^ 4 - 1382 * x ^ 3 + 686546 * x ^ 2 + 94753489 * x + 415242715820 := by linarith
  have t4 : 0 ≤ (-15 * x ^ 4 - 1382 * x ^ 3 + 686546 * x ^ 2 + 94753489 * x + 415242715820) * g ^ 4 := mul_nonneg (by linarith) (by positivity)
  have hc5 : (700673705 : ℝ) ≤ -180 * x ^ 3 + 11592 * x ^ 2 + 8441874 * x + 126785196 := by linarith
  have t5 : 0 ≤ (-180 * x ^ 3 + 11592 * x ^ 2 + 8441874 * x + 126785196) * g ^ 5 := mul_nonneg (by linarith) (by positivity)
  have hc6 : (6590560 : ℝ) ≤ -20 * x ^ 3 - 238 * x ^ 2 + 253456 * x + 577075 := by linarith
  have t6 : 0 ≤ (-20 * x ^ 3 - 238 * x ^ 2 + 253456 * x + 577075) * g ^ 6 := mul_nonneg (by linarith) (by positivity)
  have hc7 : (-2152182 : ℝ) ≤ -180 * x ^ 2 + 10296 * x - 1707786 := by linarith
  have t7 : (-2152182 : ℝ) ≤ (-180 * x ^ 2 + 10296 * x - 1707786) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-161890 : ℝ) ≤ -15 * x ^ 2 + 453 * x - 95595 := by linarith
  have t8 : (-161890 : ℝ) ≤ (-15 * x ^ 2 + 453 * x - 95595) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-4097 : ℝ) ≤ -90 * x + 3216 := by linarith
  have t9 : (-4097 : ℝ) ≤ (-90 * x + 3216) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-283 : ℝ) ≤ -6 * x + 205 := by linarith
  have t10 : (-283 : ℝ) ≤ (-6 * x + 205) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-18 : ℝ) ≤ -18 := by norm_num
  have t11 : (-18 : ℝ) ≤ (-18) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-1 : ℝ) ≤ -1 := by norm_num
  have t12 : (-1 : ℝ) ≤ (-1) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece on `[325/4, 361/4]`, proved monomial by monomial. -/
lemma coeff_six_hi (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (325 / 4 : ℝ) ≤ x) (hb : x ≤ (361 / 4 : ℝ)) :
    0 < (-x ^ 6 - 367 * x ^ 5 - 107151 * x ^ 4 - 16761109 * x ^ 3 - 1506978868 * x ^ 2 + (11533581176256 / 25) * x - (39151075590144 / 25)) +
      (-18 * x ^ 5 + 648 * x ^ 4 - 2345178 * x ^ 3 - 485468052 * x ^ 2 + 910177688544 * x - (35532666150912 / 25)) * g +
      (-6 * x ^ 5 - 1263 * x ^ 4 + 230344 * x ^ 3 - 15481975 * x ^ 2 + 410414659192 * x - (31379562529344 / 25)) * g ^ 2 +
      (-90 * x ^ 4 + 5160 * x ^ 3 + 7804482 * x ^ 2 + 59354904 * x + 81545563104) * g ^ 3 +
      (-15 * x ^ 4 - 1382 * x ^ 3 + 686546 * x ^ 2 + 94753489 * x + 415242715820) * g ^ 4 +
      (-180 * x ^ 3 + 11592 * x ^ 2 + 8441874 * x + 126785196) * g ^ 5 +
      (-20 * x ^ 3 - 238 * x ^ 2 + 253456 * x + 577075) * g ^ 6 +
      (-180 * x ^ 2 + 10296 * x - 1707786) * g ^ 7 +
      (-15 * x ^ 2 + 453 * x - 95595) * g ^ 8 +
      (-90 * x + 3216) * g ^ 9 +
      (-6 * x + 205) * g ^ 10 +
      (-18) * g ^ 11 +
      (-1) * g ^ 12 := by
  have hx : 0 ≤ x := by linarith
  have u1 : x ^ 1 ≤ (361 / 4 : ℝ) := by
    calc x ^ 1 ≤ (361 / 4 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (325 / 4 : ℝ) ≤ x ^ 1 := by
    calc (325 / 4 : ℝ) = (325 / 4 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (130321 / 16 : ℝ) := by
    calc x ^ 2 ≤ (361 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (105625 / 16 : ℝ) ≤ x ^ 2 := by
    calc (105625 / 16 : ℝ) = (325 / 4 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (47045881 / 64 : ℝ) := by
    calc x ^ 3 ≤ (361 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (34328125 / 64 : ℝ) ≤ x ^ 3 := by
    calc (34328125 / 64 : ℝ) = (325 / 4 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (16983563041 / 256 : ℝ) := by
    calc x ^ 4 ≤ (361 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (11156640625 / 256 : ℝ) ≤ x ^ 4 := by
    calc (11156640625 / 256 : ℝ) = (325 / 4 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (6131066257801 / 1024 : ℝ) := by
    calc x ^ 5 ≤ (361 / 4 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (3625908203125 / 1024 : ℝ) ≤ x ^ 5 := by
    calc (3625908203125 / 1024 : ℝ) = (325 / 4 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (2213314919066161 / 4096 : ℝ) := by
    calc x ^ 6 ≤ (361 / 4 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (1178420166015625 / 4096 : ℝ) ≤ x ^ 6 := by
    calc (1178420166015625 / 4096 : ℝ) = (325 / 4 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have hc0 : (1476362511432 : ℝ) ≤ -x ^ 6 - 367 * x ^ 5 - 107151 * x ^ 4 - 16761109 * x ^ 3 - 1506978868 * x ^ 2 + (11533581176256 / 25) * x - (39151075590144 / 25) := by linarith
  have hc1 : (66773009190517 : ℝ) ≤ -18 * x ^ 5 + 648 * x ^ 4 - 2345178 * x ^ 3 - 485468052 * x ^ 2 + 910177688544 * x - (35532666150912 / 25) := by linarith
  have t1 : 0 ≤ (-18 * x ^ 5 + 648 * x ^ 4 - 2345178 * x ^ 3 - 485468052 * x ^ 2 + 910177688544 * x - (35532666150912 / 25)) * g := mul_nonneg (by linarith) (by positivity)
  have hc2 : (31968743900242 : ℝ) ≤ -6 * x ^ 5 - 1263 * x ^ 4 + 230344 * x ^ 3 - 15481975 * x ^ 2 + 410414659192 * x - (31379562529344 / 25) := by linarith
  have t2 : 0 ≤ (-6 * x ^ 5 - 1263 * x ^ 4 + 230344 * x ^ 3 - 15481975 * x ^ 2 + 410414659192 * x - (31379562529344 / 25)) * g ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hc3 : (134686845953 : ℝ) ≤ -90 * x ^ 4 + 5160 * x ^ 3 + 7804482 * x ^ 2 + 59354904 * x + 81545563104 := by linarith
  have t3 : 0 ≤ (-90 * x ^ 4 + 5160 * x ^ 3 + 7804482 * x ^ 2 + 59354904 * x + 81545563104) * g ^ 3 := mul_nonneg (by linarith) (by positivity)
  have hc4 : (425462685489 : ℝ) ≤ -15 * x ^ 4 - 1382 * x ^ 3 + 686546 * x ^ 2 + 94753489 * x + 415242715820 := by linarith
  have t4 : 0 ≤ (-15 * x ^ 4 - 1382 * x ^ 3 + 686546 * x ^ 2 + 94753489 * x + 415242715820) * g ^ 4 := mul_nonneg (by linarith) (by positivity)
  have hc5 : (756896230 : ℝ) ≤ -180 * x ^ 3 + 11592 * x ^ 2 + 8441874 * x + 126785196 := by linarith
  have t5 : 0 ≤ (-180 * x ^ 3 + 11592 * x ^ 2 + 8441874 * x + 126785196) * g ^ 5 := mul_nonneg (by linarith) (by positivity)
  have hc6 : (4530012 : ℝ) ≤ -20 * x ^ 3 - 238 * x ^ 2 + 253456 * x + 577075 := by linarith
  have t6 : 0 ≤ (-20 * x ^ 3 - 238 * x ^ 2 + 253456 * x + 577075) * g ^ 6 := mul_nonneg (by linarith) (by positivity)
  have hc7 : (-2337348 : ℝ) ≤ -180 * x ^ 2 + 10296 * x - 1707786 := by linarith
  have t7 : (-2337348 : ℝ) ≤ (-180 * x ^ 2 + 10296 * x - 1707786) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-180965 : ℝ) ≤ -15 * x ^ 2 + 453 * x - 95595 := by linarith
  have t8 : (-180965 : ℝ) ≤ (-15 * x ^ 2 + 453 * x - 95595) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-4907 : ℝ) ≤ -90 * x + 3216 := by linarith
  have t9 : (-4907 : ℝ) ≤ (-90 * x + 3216) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-337 : ℝ) ≤ -6 * x + 205 := by linarith
  have t10 : (-337 : ℝ) ≤ (-6 * x + 205) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-18 : ℝ) ≤ -18 := by norm_num
  have t11 : (-18 : ℝ) ≤ (-18) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-1 : ℝ) ≤ -1 := by norm_num
  have t12 : (-1 : ℝ) ≤ (-1) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- The box polynomial for `H₃ = N₃ / (967680 (s - 1))`, proved. -/
lemma box_six_two_poly (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht0 : 17 / 2 ≤ t) (ht1 : t ≤ 19 / 2) :
    ((σ ^ 6 + 9 * σ ^ 5 - 15 * σ ^ 4 * t ^ 2 - 143 * σ ^ 4 - 90 * σ ^ 3 * t ^ 2 - 321 * σ ^ 3 + 15 * σ ^ 2 * t ^ 4 + 858 * σ ^ 2 * t ^ 2 + 40462 * σ ^ 2 + 45 * σ * t ^ 4 + 963 * σ * t ^ 2 + 443832 * σ - t ^ 6 - 143 * t ^ 4 - 40462 * t ^ 2 + 1451520) ^ 2 + (t * (6 * σ ^ 5 + 45 * σ ^ 4 - 20 * σ ^ 3 * t ^ 2 - 572 * σ ^ 3 - 90 * σ ^ 2 * t ^ 2 - 963 * σ ^ 2 + 6 * σ * t ^ 4 + 572 * σ * t ^ 2 + 80924 * σ + 9 * t ^ 4 + 321 * t ^ 2 + 443832)) ^ 2) <
      (76 / 100 + 2 * σ / 3) ^ 2 * 967680 ^ 2 * ((σ - 1) ^ 2 + t ^ 2) := by
  have hx0 : 289 / 4 ≤ t ^ 2 := by nlinarith
  have hx1 : t ^ 2 ≤ 361 / 4 := by nlinarith
  have h : 0 < (-(t ^ 2) ^ 6 - 367 * (t ^ 2) ^ 5 - 107151 * (t ^ 2) ^ 4 - 16761109 * (t ^ 2) ^ 3 - 1506978868 * (t ^ 2) ^ 2 + (11533581176256 / 25) * t ^ 2 - (39151075590144 / 25)) +
      (-18 * (t ^ 2) ^ 5 + 648 * (t ^ 2) ^ 4 - 2345178 * (t ^ 2) ^ 3 - 485468052 * (t ^ 2) ^ 2 + 910177688544 * t ^ 2 - (35532666150912 / 25)) * σ +
      (-6 * (t ^ 2) ^ 5 - 1263 * (t ^ 2) ^ 4 + 230344 * (t ^ 2) ^ 3 - 15481975 * (t ^ 2) ^ 2 + 410414659192 * t ^ 2 - (31379562529344 / 25)) * σ ^ 2 +
      (-90 * (t ^ 2) ^ 4 + 5160 * (t ^ 2) ^ 3 + 7804482 * (t ^ 2) ^ 2 + 59354904 * t ^ 2 + 81545563104) * σ ^ 3 +
      (-15 * (t ^ 2) ^ 4 - 1382 * (t ^ 2) ^ 3 + 686546 * (t ^ 2) ^ 2 + 94753489 * t ^ 2 + 415242715820) * σ ^ 4 +
      (-180 * (t ^ 2) ^ 3 + 11592 * (t ^ 2) ^ 2 + 8441874 * t ^ 2 + 126785196) * σ ^ 5 +
      (-20 * (t ^ 2) ^ 3 - 238 * (t ^ 2) ^ 2 + 253456 * t ^ 2 + 577075) * σ ^ 6 +
      (-180 * (t ^ 2) ^ 2 + 10296 * t ^ 2 - 1707786) * σ ^ 7 +
      (-15 * (t ^ 2) ^ 2 + 453 * t ^ 2 - 95595) * σ ^ 8 +
      (-90 * t ^ 2 + 3216) * σ ^ 9 +
      (-6 * t ^ 2 + 205) * σ ^ 10 +
      (-18) * σ ^ 11 +
      (-1) * σ ^ 12 := by
    rcases le_total (t ^ 2) (325 / 4) with hl | hl
    · exact coeff_six_lo σ (t ^ 2) h0 h1 hx0 hl
    · exact coeff_six_hi σ (t ^ 2) h0 h1 hl hx1
  have e : (76 / 100 + 2 * σ / 3) ^ 2 * 967680 ^ 2 * ((σ - 1) ^ 2 + t ^ 2) -
      ((σ ^ 6 + 9 * σ ^ 5 - 15 * σ ^ 4 * t ^ 2 - 143 * σ ^ 4 - 90 * σ ^ 3 * t ^ 2 - 321 * σ ^ 3 + 15 * σ ^ 2 * t ^ 4 + 858 * σ ^ 2 * t ^ 2 + 40462 * σ ^ 2 + 45 * σ * t ^ 4 + 963 * σ * t ^ 2 + 443832 * σ - t ^ 6 - 143 * t ^ 4 - 40462 * t ^ 2 + 1451520) ^ 2 + (t * (6 * σ ^ 5 + 45 * σ ^ 4 - 20 * σ ^ 3 * t ^ 2 - 572 * σ ^ 3 - 90 * σ ^ 2 * t ^ 2 - 963 * σ ^ 2 + 6 * σ * t ^ 4 + 572 * σ * t ^ 2 + 80924 * σ + 9 * t ^ 4 + 321 * t ^ 2 + 443832)) ^ 2) =
      (-(t ^ 2) ^ 6 - 367 * (t ^ 2) ^ 5 - 107151 * (t ^ 2) ^ 4 - 16761109 * (t ^ 2) ^ 3 - 1506978868 * (t ^ 2) ^ 2 + (11533581176256 / 25) * t ^ 2 - (39151075590144 / 25)) +
      (-18 * (t ^ 2) ^ 5 + 648 * (t ^ 2) ^ 4 - 2345178 * (t ^ 2) ^ 3 - 485468052 * (t ^ 2) ^ 2 + 910177688544 * t ^ 2 - (35532666150912 / 25)) * σ +
      (-6 * (t ^ 2) ^ 5 - 1263 * (t ^ 2) ^ 4 + 230344 * (t ^ 2) ^ 3 - 15481975 * (t ^ 2) ^ 2 + 410414659192 * t ^ 2 - (31379562529344 / 25)) * σ ^ 2 +
      (-90 * (t ^ 2) ^ 4 + 5160 * (t ^ 2) ^ 3 + 7804482 * (t ^ 2) ^ 2 + 59354904 * t ^ 2 + 81545563104) * σ ^ 3 +
      (-15 * (t ^ 2) ^ 4 - 1382 * (t ^ 2) ^ 3 + 686546 * (t ^ 2) ^ 2 + 94753489 * t ^ 2 + 415242715820) * σ ^ 4 +
      (-180 * (t ^ 2) ^ 3 + 11592 * (t ^ 2) ^ 2 + 8441874 * t ^ 2 + 126785196) * σ ^ 5 +
      (-20 * (t ^ 2) ^ 3 - 238 * (t ^ 2) ^ 2 + 253456 * t ^ 2 + 577075) * σ ^ 6 +
      (-180 * (t ^ 2) ^ 2 + 10296 * t ^ 2 - 1707786) * σ ^ 7 +
      (-15 * (t ^ 2) ^ 2 + 453 * t ^ 2 - 95595) * σ ^ 8 +
      (-90 * t ^ 2 + 3216) * σ ^ 9 +
      (-6 * t ^ 2 + 205) * σ ^ 10 +
      (-18) * σ ^ 11 +
      (-1) * σ ^ 12 := by ring
  linarith

/-- The main term is small: `‖H₃(s)‖ < 76/100 + 2σ/3` on `(0,1) × (17/2, 19/2]`. Proved. -/
lemma main_six_two_lt (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 17 / 2 < s.im)
    (ht1 : s.im ≤ 19 / 2) :
    ‖1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 +
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680‖ < 76 / 100 + 2 * s.re / 3 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hM : 1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 +
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680 =
      (483840 * (s - 1) + 1935360 + 40320 * s * (s - 1) - 168 * (s - 1) * s * (s + 1) * (s + 2) +
        (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) / (967680 * (s - 1)) := by
    field_simp
    ring
  rw [hM, norm_div, norm_mul, Complex.norm_ofNat]
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  rw [div_lt_iff₀ (by positivity)]
  set P : ℂ := 483840 * (s - 1) + 1935360 + 40320 * s * (s - 1) -
    168 * (s - 1) * s * (s + 1) * (s + 2) + (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4)
    with hP
  have hPre : P.re = s.re ^ 6 + 9 * s.re ^ 5 - 15 * s.re ^ 4 * s.im ^ 2 - 143 * s.re ^ 4 - 90 * s.re ^ 3 * s.im ^ 2 - 321 * s.re ^ 3 + 15 * s.re ^ 2 * s.im ^ 4 + 858 * s.re ^ 2 * s.im ^ 2 + 40462 * s.re ^ 2 + 45 * s.re * s.im ^ 4 + 963 * s.re * s.im ^ 2 + 443832 * s.re - s.im ^ 6 - 143 * s.im ^ 4 - 40462 * s.im ^ 2 + 1451520 := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hPim : P.im = s.im * (6 * s.re ^ 5 + 45 * s.re ^ 4 - 20 * s.re ^ 3 * s.im ^ 2 - 572 * s.re ^ 3 - 90 * s.re ^ 2 * s.im ^ 2 - 963 * s.re ^ 2 + 6 * s.re * s.im ^ 4 + 572 * s.re * s.im ^ 2 + 80924 * s.re + 9 * s.im ^ 4 + 321 * s.im ^ 2 + 443832) := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hc : 0 < (76 / 100 + 2 * s.re / 3) * (967680 * ‖s - 1‖) := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 hc.le
  have e1 : ((76 / 100 + 2 * s.re / 3) * (967680 * ‖s - 1‖)) ^ 2 =
      (76 / 100 + 2 * s.re / 3) ^ 2 * 967680 ^ 2 * ((s.re - 1) ^ 2 + s.im ^ 2) := by
    rw [mul_pow, mul_pow, hsq (s - 1)]
    simp
    ring
  rw [e1, hsq P, hPre, hPim]
  exact box_six_two_poly s.re s.im h0.le h1.le ht0.le ht1

/-- The remainder factor: `‖s‖ ⋯ ‖s+5‖ ≤ 1148744` on the box. Proved. -/
lemma prod_six_two_le (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 17 / 2 < s.im)
    (ht1 : s.im ≤ 19 / 2) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ ≤ 1148744 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have ht2 : s.im ^ 2 ≤ 361 / 4 := by nlinarith
  have n0 : ‖s‖ ^ 2 ≤ 365 / 4 := by rw [hsq]; nlinarith
  have n1 : ‖s + 1‖ ^ 2 ≤ 377 / 4 := by
    rw [hsq]; simp only [add_re, one_re, add_im, one_im]; nlinarith
  have n2 : ‖s + 2‖ ^ 2 ≤ 397 / 4 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n3 : ‖s + 3‖ ^ 2 ≤ 425 / 4 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n4 : ‖s + 4‖ ^ 2 ≤ 461 / 4 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n5 : ‖s + 5‖ ^ 2 ≤ 505 / 4 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have hsq' : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖) ^ 2 ≤
      365 / 4 * (377 / 4) * (397 / 4) * (425 / 4) * (461 / 4) * (505 / 4) := by
    have e : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖) ^ 2 =
        ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 * ‖s + 4‖ ^ 2 * ‖s + 5‖ ^ 2 := by ring
    rw [e]
    have q1 := mul_le_mul n0 n1 (by positivity) (by norm_num)
    have q2 := mul_le_mul q1 n2 (by positivity) (by norm_num)
    have q3 := mul_le_mul q2 n3 (by positivity) (by norm_num)
    have q4 := mul_le_mul q3 n4 (by positivity) (by norm_num)
    exact mul_le_mul q4 n5 (by positivity) (by norm_num)
  have : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖) ^ 2 ≤ 1148744 ^ 2 := by
    refine hsq'.trans ?_; norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).mp this

/-- PROVED: `ζ` has no zero with `0 < Re ρ < 1` and `17/2 < Im ρ ≤ 19/2`, same argument as
`riemannZeta_ne_zero_eight_seventeen_half` with the three term formula. -/
theorem riemannZeta_ne_zero_seventeen_half_nineteen_half (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht0 : 17 / 2 < ρ.im) (ht1 : ρ.im ≤ 19 / 2) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM6_two h0 hρ1
  set I := ∫ x in Ioi (2 : ℝ),
    ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
      1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 6) with hI
  set H := 1 / 2 + 2 / (ρ - 1) + ρ / 24 - ρ * (ρ + 1) * (ρ + 2) / 5760 +
    ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) / 967680 with hH
  set Q := ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) / 2 * I with hQ
  have hkey : (2 : ℂ) ^ (-ρ) * H = Q - 1 := by
    rw [hz] at hEM; linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / 15120 * (2 : ℝ) ^ ((-ρ - 6).re + 1) / (-(-ρ - 6).re - 1) :=
    norm_weight_int_le2 (by fun_prop) abs_B6_le (by simp; linarith)
  have hre1 : (-ρ - 6).re + 1 = -ρ.re - 5 := by simp; ring
  have hre2 : (-(-ρ - 6).re - 1) = ρ.re + 5 := by simp; ring
  rw [hre1, hre2] at hIle
  have hn2 : ‖(2 : ℂ) ^ (-ρ)‖ = (2 : ℝ) ^ (-ρ.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (-ρ)
    simpa using this
  have hP := prod_six_two_le ρ h0 h1 ht0 ht1
  have hσ : 0 < ρ.re + 5 := by linarith
  have hQle : ‖Q‖ ≤ 1148744 / 2 * (1 / 15120 * (2 : ℝ) ^ (-ρ.re - 5) / (ρ.re + 5)) := by
    rw [hQ, norm_mul, norm_div, Complex.norm_ofNat, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_mul]
    have hIn : 0 ≤ ‖I‖ := norm_nonneg _
    calc ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ / 2 * ‖I‖
        ≤ 1148744 / 2 * ‖I‖ := by
          apply mul_le_mul_of_nonneg_right _ hIn; linarith
      _ ≤ 1148744 / 2 * (1 / 15120 * (2 : ℝ) ^ (-ρ.re - 5) / (ρ.re + 5)) :=
          mul_le_mul_of_nonneg_left hIle (by norm_num)
  have hsplit : (2 : ℝ) ^ (-ρ.re - 5) = (2 : ℝ) ^ (-ρ.re) / 32 := by
    rw [sub_eq_add_neg, Real.rpow_add two_pos]
    rw [show (-(5 : ℝ)) = ((-5 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
    ring
  have hu : (2 : ℝ) ^ ρ.re * (2 : ℝ) ^ (-ρ.re) = 1 := by
    rw [← Real.rpow_add two_pos]; simp
  have hupos : 0 < (2 : ℝ) ^ ρ.re := Real.rpow_pos_of_pos two_pos _
  have hlow : 1 - ‖Q‖ ≤ (2 : ℝ) ^ (-ρ.re) * ‖H‖ := by
    have ha := norm_sub_norm_le (1 : ℂ) Q
    rw [norm_sub_rev, norm_one] at ha
    have hb : ‖Q - 1‖ = (2 : ℝ) ^ (-ρ.re) * ‖H‖ := by
      rw [← hkey, norm_mul, hn2]
    linarith
  have hE : (2 : ℝ) ^ ρ.re * ‖Q‖ ≤ 24 / 100 := by
    have := mul_le_mul_of_nonneg_left hQle hupos.le
    rw [hsplit] at this
    have e : (2 : ℝ) ^ ρ.re * (1148744 / 2 * (1 / 15120 * ((2 : ℝ) ^ (-ρ.re) / 32) / (ρ.re + 5))) =
        1148744 / 967680 / (ρ.re + 5) * ((2 : ℝ) ^ ρ.re * (2 : ℝ) ^ (-ρ.re)) := by
      field_simp
      ring
    rw [e, hu, mul_one] at this
    have : 1148744 / 967680 / (ρ.re + 5) ≤ 24 / 100 := by
      rw [div_le_iff₀ hσ]; nlinarith
    linarith
  have hH2 : (2 : ℝ) ^ ρ.re - 24 / 100 ≤ ‖H‖ := by
    have := mul_le_mul_of_nonneg_left hlow hupos.le
    have e : (2 : ℝ) ^ ρ.re * ((2 : ℝ) ^ (-ρ.re) * ‖H‖) = ‖H‖ := by
      rw [← mul_assoc, hu, one_mul]
    rw [e, mul_sub, mul_one] at this
    linarith
  have hlo := two_rpow_ge ρ.re h0.le
  have hup := main_six_two_lt ρ h0 h1 ht0 ht1
  rw [← hH] at hup
  linarith

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914, read on the window `(19/2, 21/2]`: no zero
of `ζ` in the open strip has ordinate in `(19/2, 21/2]`. Class MEDIUM: the route of this file with
five to six Bernoulli terms, grid margin about `0.06` near `21/2`, S137 numerics. -/
theorem zeta_zero_free_nineteen_half_ten_half (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 19 / 2 < ρ.im) : 21 / 2 < ρ.im := by
  sorry

/-- `Feed1122ZetaBaseTwo.zeta_zero_free_seventeen_half_ten_half`, exactly its statement, from the
proved range `(17/2, 19/2]` and the MEDIUM leaf on `(19/2, 21/2]`. -/
theorem zeta_zero_free_seventeen_half_ten_half_s137 (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : 17 / 2 < ρ.im) : 21 / 2 < ρ.im := by
  by_cases h : ρ.im ≤ 19 / 2
  · exact absurd h0 (riemannZeta_ne_zero_seventeen_half_nineteen_half ρ hre0 hre1 him h)
  · exact zeta_zero_free_nineteen_half_ten_half ρ h0 hre0 hre1 (not_le.mp h)

end LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoSix

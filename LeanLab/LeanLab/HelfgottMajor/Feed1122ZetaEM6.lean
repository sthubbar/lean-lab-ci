import LeanLab.HelfgottMajor.Feed1122ZetaFourSix

/-!
# Split of `zeta_zero_free_six_fourteen` at height `15/2`, burst 20261122 S137

`Feed1122ZetaFourSix` leaves the HARD LEAF `zeta_zero_free_six_fourteen`: no zero of `ζ` in the
open strip has ordinate in `(6, 14]`, Helfgott arXiv 1305.2897v4 Section 4.6 page 56 with
Platt's verification and the first zero tables of Gram 1903 and Backlund 1914.

One more Bernoulli term, Edwards, Riemann's Zeta Function, 1974, Chapter 6, display of the
Euler Maclaurin formula with `N = 1`:
`ζ(s) = (s+2)(s+3)/(12(s-1)) - s(s+1)(s+2)/720 + s(s+1)(s+2)(s+3)(s+4)/30240
  - s(s+1)⋯(s+5)/2 ∫_1^∞ (B₆({u})/360) u^(-s-6) du`, valid in `Re s > 0`.

* PROVED `ibp5`, `ibp6`, `riemannZeta_eq_EM6`: that formula, from `riemannZeta_eq_EM4` by two
  more integrations by parts, `ibp_gen`.
* PROVED `abs_B6_le`: `|B₆({u})| ≤ 1/42`, since `B₆(y) = 1/42 - u³ - u²/2` with `u = y(1-y)`.
* PROVED `coeff6_pos_low`, `coeff6_pos_high`, `box6_poly_pos`: a polynomial certificate, the
  coefficients in `x = t²` of the box polynomial bounded monomial by monomial on `[36, 49]` and
  `[49, 225/4]`, the leading one through `x⁵ (x² + 31x - 1797)`.
* PROVED `riemannZeta_ne_zero_six_seven_half`: no zero with ordinate in `(6, 15/2]`.
* LEAF HARD `zeta_zero_free_seven_half_fourteen`: no zero with ordinate in `(15/2, 14]`.
* PROVED assembly `zeta_zero_free_six_fourteen_s137`, exactly the statement of
  `Feed1122ZetaFourSix.zeta_zero_free_six_fourteen`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaEM6
open Complex Set MeasureTheory LeanLab.HelfgottMajor.Feed1122ZetaEM4

/-- `|B₅({x})/60| ≤ 1`, a crude bound. -/
lemma abs_B5_le (x : ℝ) :
    |((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 + 5 / 3 * (Int.fract x) ^ 3 -
      1 / 6 * Int.fract x) / 60| ≤ 1 := by
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  set y := Int.fract x
  have p2 : y ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have p3 : y ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have p4 : y ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have p5 : y ^ 5 ≤ 1 := pow_le_one₀ h0 h1
  have q2 : 0 ≤ y ^ 2 := by positivity
  have q3 : 0 ≤ y ^ 3 := by positivity
  have q4 : 0 ≤ y ^ 4 := by positivity
  have q5 : 0 ≤ y ^ 5 := by positivity
  rw [abs_le]; constructor <;> linarith

/-- `|B₆({x})/360| ≤ 1/15120`, since `B₆(y) = 1/42 - u³ - u²/2` with `u = y(1-y) ∈ [0, 1/4]`. -/
lemma abs_B6_le (x : ℝ) :
    |((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
      1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360| ≤ 1 / 15120 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  set y := Int.fract x
  have e : y ^ 6 - 3 * y ^ 5 + 5 / 2 * y ^ 4 - 1 / 2 * y ^ 2 + 1 / 42 =
      1 / 42 - (y * (1 - y)) ^ 3 - (y * (1 - y)) ^ 2 / 2 := by ring
  have hu : 0 ≤ y * (1 - y) := mul_nonneg h0 (by linarith)
  have hu' : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have u2 : (y * (1 - y)) ^ 2 ≤ 1 / 16 := by nlinarith
  have u3 : (y * (1 - y)) ^ 3 ≤ 1 / 64 := by nlinarith
  have u2' : 0 ≤ (y * (1 - y)) ^ 2 := by positivity
  have u3' : 0 ≤ (y * (1 - y)) ^ 3 := by positivity
  rw [e, abs_le]; constructor <;> linarith

/-- step five: `∫ (B₄/12) x^(-s-4) = (s+4) ∫ (B₅/60) x^(-s-5)`. -/
lemma ibp5 {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 4 - 2 * (Int.fract x) ^ 3 +
        (Int.fract x) ^ 2 - 1 / 30) / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 4)) =
      (s + 4) * ∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 +
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
  have h := ibp_gen hc hd (by fun_prop) (by fun_prop) abs_B5_le abs_B4_le
    (P0 := 0) (by intro n; simp) (a := -s - 4) (by simp; linarith)
  have e : (-s - 4 - 1) = -s - 5 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- step six: `∫ (B₅/60) x^(-s-5) = -1/15120 + (s+5) ∫ (B₆/360) x^(-s-6)`. -/
lemma ibp6 {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 5 - 5 / 2 * (Int.fract x) ^ 4 +
        5 / 3 * (Int.fract x) ^ 3 - 1 / 6 * Int.fract x) / 60 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 5)) =
      -1 / 15120 + (s + 5) * ∫ x in Ioi (1 : ℝ), ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 +
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
  have h := ibp_gen hc hd (by fun_prop) (by fun_prop) abs_B6_le abs_B5_le
    (P0 := 1 / 15120) (by intro n; simp; norm_num) (a := -s - 5) (by simp; linarith)
  have e : (-s - 5 - 1) = -s - 6 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- third order Euler Maclaurin with `N = 1`, Edwards 1974 Chapter 6. -/
theorem riemannZeta_eq_EM6 {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 +
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240 -
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) / 2 * ∫ x in Ioi (1 : ℝ),
        ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
          1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 6) := by
  rw [riemannZeta_eq_EM4 hs h1, ibp5 hs, ibp6 hs]
  ring

set_option maxHeartbeats 4000000 in
lemma coeff6_pos_low (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (36 : ℝ) ≤ x) (hb : x ≤ (49 : ℝ)) :
    0 < (-x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000) +
      (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g +
      (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 +
      (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 +
      (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 +
      (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 +
      (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 +
      (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 +
      (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 +
      (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 +
      (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 +
      (-18 * x - 1764) * g ^ 11 +
      (-x - 84) * g ^ 12 := by
  have hx : 0 ≤ x := by linarith
  have u1 : x ^ 1 ≤ 49 := by
    calc x ^ 1 ≤ (49 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (36 : ℝ) ≤ x ^ 1 := by
    calc (36 : ℝ) = (36 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ 2401 := by
    calc x ^ 2 ≤ (49 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (1296 : ℝ) ≤ x ^ 2 := by
    calc (1296 : ℝ) = (36 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ 117649 := by
    calc x ^ 3 ≤ (49 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (46656 : ℝ) ≤ x ^ 3 := by
    calc (46656 : ℝ) = (36 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ 5764801 := by
    calc x ^ 4 ≤ (49 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (1679616 : ℝ) ≤ x ^ 4 := by
    calc (1679616 : ℝ) = (36 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ 282475249 := by
    calc x ^ 5 ≤ (49 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (60466176 : ℝ) ≤ x ^ 5 := by
    calc (60466176 : ℝ) = (36 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ 13841287201 := by
    calc x ^ 6 ≤ (49 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (2176782336 : ℝ) ≤ x ^ 6 := by
    calc (2176782336 : ℝ) = (36 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ 678223072849 := by
    calc x ^ 7 ≤ (49 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (78364164096 : ℝ) ≤ x ^ 7 := by
    calc (78364164096 : ℝ) = (36 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (2123 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(2123 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (327541258213 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (273537122670 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-78382202284 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-78382202284 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-72568748484 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-72568748484 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-25710886110 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-25710886110 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-4859946714 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-4859946714 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-673653043 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-673653043 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-64012242 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-64012242 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-5559897 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-5559897 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-428526 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-428526 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-41237 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-41237 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2646 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2646 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-133 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-133 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
lemma coeff6_pos_high (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (49 : ℝ) ≤ x) (hb : x ≤ (225 / 4 : ℝ)) :
    0 < (-x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000) +
      (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g +
      (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 +
      (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 +
      (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 +
      (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 +
      (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 +
      (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 +
      (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 +
      (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 +
      (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 +
      (-18 * x - 1764) * g ^ 11 +
      (-x - 84) * g ^ 12 := by
  have hx : 0 ≤ x := by linarith
  have u1 : x ^ 1 ≤ (225 / 4 : ℝ) := by
    calc x ^ 1 ≤ (225 / 4 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (49 : ℝ) ≤ x ^ 1 := by
    calc (49 : ℝ) = (49 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (50625 / 16 : ℝ) := by
    calc x ^ 2 ≤ (225 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (2401 : ℝ) ≤ x ^ 2 := by
    calc (2401 : ℝ) = (49 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (11390625 / 64 : ℝ) := by
    calc x ^ 3 ≤ (225 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (117649 : ℝ) ≤ x ^ 3 := by
    calc (117649 : ℝ) = (49 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (2562890625 / 256 : ℝ) := by
    calc x ^ 4 ≤ (225 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (5764801 : ℝ) ≤ x ^ 4 := by
    calc (5764801 : ℝ) = (49 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (576650390625 / 1024 : ℝ) := by
    calc x ^ 5 ≤ (225 / 4 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (282475249 : ℝ) ≤ x ^ 5 := by
    calc (282475249 : ℝ) = (49 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (129746337890625 / 4096 : ℝ) := by
    calc x ^ 6 ≤ (225 / 4 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (13841287201 : ℝ) ≤ x ^ 6 := by
    calc (13841287201 : ℝ) = (49 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (29192926025390625 / 16384 : ℝ) := by
    calc x ^ 7 ≤ (225 / 4 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (678223072849 : ℝ) ≤ x ^ 7 := by
    calc (678223072849 : ℝ) = (49 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (49773 / 16 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(49773 / 16 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (563452313855 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (651178260184 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-185304363172 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-185304363172 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-117024914185 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-117024914185 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-38548432445 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-38548432445 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-6709756215 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-6709756215 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-912715670 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-912715670 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-84526424 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-84526424 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-7467825 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-7467825 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-540876 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-540876 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-48593 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-48593 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2777 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2777 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-141 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-141 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- The box polynomial of the three term formula: `|P₃|² (σ+5)²` beats
`|s-1|² |s|² ⋯ |s+5|²` on `[0,1] × [6, 15/2]`, written with `Re P₃` and `Im P₃`. Proved. -/
lemma box6_poly_pos (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht0 : 6 ≤ t) (ht1 : t ≤ 15 / 2) :
    ((σ - 1) ^ 2 + t ^ 2) * (σ ^ 2 + t ^ 2) * ((σ + 1) ^ 2 + t ^ 2) * ((σ + 2) ^ 2 + t ^ 2) *
        ((σ + 3) ^ 2 + t ^ 2) * ((σ + 4) ^ 2 + t ^ 2) * ((σ + 5) ^ 2 + t ^ 2) <
      ((σ ^ 6 + 9 * σ ^ 5 - 15 * σ ^ 4 * t ^ 2 - 17 * σ ^ 4 - 90 * σ ^ 3 * t ^ 2 - 69 * σ ^ 3 + 15 * σ ^ 2 * t ^ 4 + 102 * σ ^ 2 * t ^ 2 + 2536 * σ ^ 2 + 45 * σ * t ^ 4 + 207 * σ * t ^ 2 + 12660 * σ - t ^ 6 - 17 * t ^ 4 - 2536 * t ^ 2 + 15120) ^ 2 +
          (t * (6 * σ ^ 5 + 45 * σ ^ 4 - 20 * σ ^ 3 * t ^ 2 - 68 * σ ^ 3 - 90 * σ ^ 2 * t ^ 2 - 207 * σ ^ 2 + 6 * σ * t ^ 4 + 68 * σ * t ^ 2 + 5072 * σ + 9 * t ^ 4 + 69 * t ^ 2 + 12660)) ^ 2) *
        (σ + 5) ^ 2 := by
  have hx0 : 36 ≤ t ^ 2 := by nlinarith
  have hx1 : t ^ 2 ≤ 225 / 4 := by nlinarith
  have h : 0 < (-(t ^ 2) ^ 7 - 31 * (t ^ 2) ^ 6 + 1797 * (t ^ 2) ^ 5 + 156407 * (t ^ 2) ^ 4 + 7186904 * (t ^ 2) ^ 3 + 191571924 * (t ^ 2) ^ 2 + 2089659600 * t ^ 2 + 5715360000) +
      (-18 * (t ^ 2) ^ 6 + 480 * (t ^ 2) ^ 5 + 54786 * (t ^ 2) ^ 4 + 2624700 * (t ^ 2) ^ 3 + 134111052 * (t ^ 2) ^ 2 + 2597612640 * t ^ 2 + 11857104000) * σ +
      (-6 * (t ^ 2) ^ 6 - 171 * (t ^ 2) ^ 5 + 7912 * (t ^ 2) ^ 4 - 286123 * (t ^ 2) ^ 3 + 15919168 * (t ^ 2) ^ 2 + 1186928328 * t ^ 2 + 9981090000) * σ ^ 2 +
      (-90 * (t ^ 2) ^ 5 + 708 * (t ^ 2) ^ 4 - 244902 * (t ^ 2) ^ 3 - 12411588 * (t ^ 2) ^ 2 + 165888504 * t ^ 2 + 4305567840) * σ ^ 3 +
      (-15 * (t ^ 2) ^ 5 - 458 * (t ^ 2) ^ 4 - 35686 * (t ^ 2) ^ 3 - 5448683 * (t ^ 2) ^ 2 - 51331096 * t ^ 2 + 962455284) * σ ^ 4 +
      (-180 * (t ^ 2) ^ 4 - 2520 * (t ^ 2) ^ 3 - 976542 * (t ^ 2) ^ 2 - 25965276 * t ^ 2 + 91168812) * σ ^ 5 +
      (-20 * (t ^ 2) ^ 4 - 742 * (t ^ 2) ^ 3 - 95984 * (t ^ 2) ^ 2 - 4982969 * t ^ 2 + 3561600) * σ ^ 6 +
      (-180 * (t ^ 2) ^ 3 - 7008 * (t ^ 2) ^ 2 - 594114 * t ^ 2 + 3102372) * σ ^ 7 +
      (-15 * (t ^ 2) ^ 3 - 723 * (t ^ 2) ^ 2 - 62247 * t ^ 2 + 990864) * σ ^ 8 +
      (-90 * (t ^ 2) ^ 2 - 6024 * t ^ 2 + 82740) * σ ^ 9 +
      (-6 * (t ^ 2) ^ 2 - 383 * t ^ 2 - 8064) * σ ^ 10 +
      (-18 * t ^ 2 - 1764) * σ ^ 11 +
      (-t ^ 2 - 84) * σ ^ 12 := by
    rcases le_total (t ^ 2) 49 with hl | hl
    · exact coeff6_pos_low σ (t ^ 2) h0 h1 hx0 hl
    · exact coeff6_pos_high σ (t ^ 2) h0 h1 hl hx1
  have e : ((σ ^ 6 + 9 * σ ^ 5 - 15 * σ ^ 4 * t ^ 2 - 17 * σ ^ 4 - 90 * σ ^ 3 * t ^ 2 - 69 * σ ^ 3 + 15 * σ ^ 2 * t ^ 4 + 102 * σ ^ 2 * t ^ 2 + 2536 * σ ^ 2 + 45 * σ * t ^ 4 + 207 * σ * t ^ 2 + 12660 * σ - t ^ 6 - 17 * t ^ 4 - 2536 * t ^ 2 + 15120) ^ 2 +
          (t * (6 * σ ^ 5 + 45 * σ ^ 4 - 20 * σ ^ 3 * t ^ 2 - 68 * σ ^ 3 - 90 * σ ^ 2 * t ^ 2 - 207 * σ ^ 2 + 6 * σ * t ^ 4 + 68 * σ * t ^ 2 + 5072 * σ + 9 * t ^ 4 + 69 * t ^ 2 + 12660)) ^ 2) *
        (σ + 5) ^ 2 -
      ((σ - 1) ^ 2 + t ^ 2) * (σ ^ 2 + t ^ 2) * ((σ + 1) ^ 2 + t ^ 2) * ((σ + 2) ^ 2 + t ^ 2) *
        ((σ + 3) ^ 2 + t ^ 2) * ((σ + 4) ^ 2 + t ^ 2) * ((σ + 5) ^ 2 + t ^ 2) =
      (-(t ^ 2) ^ 7 - 31 * (t ^ 2) ^ 6 + 1797 * (t ^ 2) ^ 5 + 156407 * (t ^ 2) ^ 4 + 7186904 * (t ^ 2) ^ 3 + 191571924 * (t ^ 2) ^ 2 + 2089659600 * t ^ 2 + 5715360000) +
        (-18 * (t ^ 2) ^ 6 + 480 * (t ^ 2) ^ 5 + 54786 * (t ^ 2) ^ 4 + 2624700 * (t ^ 2) ^ 3 + 134111052 * (t ^ 2) ^ 2 + 2597612640 * t ^ 2 + 11857104000) * σ +
        (-6 * (t ^ 2) ^ 6 - 171 * (t ^ 2) ^ 5 + 7912 * (t ^ 2) ^ 4 - 286123 * (t ^ 2) ^ 3 + 15919168 * (t ^ 2) ^ 2 + 1186928328 * t ^ 2 + 9981090000) * σ ^ 2 +
        (-90 * (t ^ 2) ^ 5 + 708 * (t ^ 2) ^ 4 - 244902 * (t ^ 2) ^ 3 - 12411588 * (t ^ 2) ^ 2 + 165888504 * t ^ 2 + 4305567840) * σ ^ 3 +
        (-15 * (t ^ 2) ^ 5 - 458 * (t ^ 2) ^ 4 - 35686 * (t ^ 2) ^ 3 - 5448683 * (t ^ 2) ^ 2 - 51331096 * t ^ 2 + 962455284) * σ ^ 4 +
        (-180 * (t ^ 2) ^ 4 - 2520 * (t ^ 2) ^ 3 - 976542 * (t ^ 2) ^ 2 - 25965276 * t ^ 2 + 91168812) * σ ^ 5 +
        (-20 * (t ^ 2) ^ 4 - 742 * (t ^ 2) ^ 3 - 95984 * (t ^ 2) ^ 2 - 4982969 * t ^ 2 + 3561600) * σ ^ 6 +
        (-180 * (t ^ 2) ^ 3 - 7008 * (t ^ 2) ^ 2 - 594114 * t ^ 2 + 3102372) * σ ^ 7 +
        (-15 * (t ^ 2) ^ 3 - 723 * (t ^ 2) ^ 2 - 62247 * t ^ 2 + 990864) * σ ^ 8 +
        (-90 * (t ^ 2) ^ 2 - 6024 * t ^ 2 + 82740) * σ ^ 9 +
        (-6 * (t ^ 2) ^ 2 - 383 * t ^ 2 - 8064) * σ ^ 10 +
        (-18 * t ^ 2 - 1764) * σ ^ 11 +
        (-t ^ 2 - 84) * σ ^ 12 := by ring
  linarith


/-- PROVED: the box inequality for the three term formula on `0 < Re s < 1`,
`6 < Im s ≤ 15/2`. -/
lemma zeta_box_six_seven_half_ineq (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 6 < s.im)
    (ht1 : s.im ≤ 15 / 2) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ / (30240 * (s.re + 5)) <
      ‖(s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 +
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240‖ := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hM : (s + 2) * (s + 3) / (12 * (s - 1)) - s * (s + 1) * (s + 2) / 720 +
        s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 30240 =
      (2520 * (s + 2) * (s + 3) - 42 * (s - 1) * s * (s + 1) * (s + 2) +
        (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) / (30240 * (s - 1)) := by
    field_simp
    ring
  rw [hM, norm_div, norm_mul, Complex.norm_ofNat]
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  have hσ5 : 0 < s.re + 5 := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  set P : ℂ := 2520 * (s + 2) * (s + 3) - 42 * (s - 1) * s * (s + 1) * (s + 2) +
    (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4) with hP
  have hPre : P.re = s.re ^ 6 + 9 * s.re ^ 5 - 15 * s.re ^ 4 * s.im ^ 2 - 17 * s.re ^ 4 - 90 * s.re ^ 3 * s.im ^ 2 - 69 * s.re ^ 3 + 15 * s.re ^ 2 * s.im ^ 4 + 102 * s.re ^ 2 * s.im ^ 2 + 2536 * s.re ^ 2 + 45 * s.re * s.im ^ 4 + 207 * s.re * s.im ^ 2 + 12660 * s.re - s.im ^ 6 - 17 * s.im ^ 4 - 2536 * s.im ^ 2 + 15120 := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hPim : P.im = s.im * (6 * s.re ^ 5 + 45 * s.re ^ 4 - 20 * s.re ^ 3 * s.im ^ 2 - 68 * s.re ^ 3 - 90 * s.re ^ 2 * s.im ^ 2 - 207 * s.re ^ 2 + 6 * s.re * s.im ^ 4 + 68 * s.re * s.im ^ 2 + 5072 * s.re + 9 * s.im ^ 4 + 69 * s.im ^ 2 + 12660) := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  suffices key : ‖s - 1‖ * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖) <
      ‖P‖ * (s.re + 5) by
    nlinarith
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  have e1 : (‖s - 1‖ * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖)) ^ 2 =
      ((s.re - 1) ^ 2 + s.im ^ 2) * (s.re ^ 2 + s.im ^ 2) * ((s.re + 1) ^ 2 + s.im ^ 2) *
        ((s.re + 2) ^ 2 + s.im ^ 2) * ((s.re + 3) ^ 2 + s.im ^ 2) *
        ((s.re + 4) ^ 2 + s.im ^ 2) * ((s.re + 5) ^ 2 + s.im ^ 2) := by
    rw [show (‖s - 1‖ * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖)) ^ 2 =
        ‖s - 1‖ ^ 2 * ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 * ‖s + 4‖ ^ 2 *
          ‖s + 5‖ ^ 2 by ring]
    rw [hsq (s - 1), hsq s, hsq (s + 1), hsq (s + 2), hsq (s + 3), hsq (s + 4), hsq (s + 5)]
    simp
  have e2 : (‖P‖ * (s.re + 5)) ^ 2 = (P.re ^ 2 + P.im ^ 2) * (s.re + 5) ^ 2 := by
    rw [mul_pow, hsq P]
  rw [e1, e2, hPre, hPim]
  exact box6_poly_pos s.re s.im h0.le h1.le ht0.le ht1

/-- PROVED: `ζ` has no zero with `0 < Re ρ < 1` and `6 < Im ρ ≤ 15/2`, from the third order
formula `riemannZeta_eq_EM6`, the remainder bound `‖∫‖ ≤ 1/(15120(Re ρ + 5))` and the box
inequality `zeta_box_six_seven_half_ineq`. -/
theorem riemannZeta_ne_zero_six_seven_half (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht0 : 6 < ρ.im) (ht1 : ρ.im ≤ 15 / 2) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM6 h0 hρ1
  set I := ∫ x in Ioi (1 : ℝ),
    ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 -
      1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 6) with hI
  have hmain : (ρ + 2) * (ρ + 3) / (12 * (ρ - 1)) - ρ * (ρ + 1) * (ρ + 2) / 720 +
      ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) / 30240 =
      ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) / 2 * I := by
    rw [hz] at hEM; linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / 15120 / (-(-ρ - 6).re - 1) :=
    norm_weight_int_le (by fun_prop) abs_B6_le (by simp; linarith)
  have hre : (-(-ρ - 6).re - 1) = ρ.re + 5 := by simp; ring
  rw [hre] at hIle
  have hlt := zeta_box_six_seven_half_ineq ρ h0 h1 ht0 ht1
  rw [hmain, norm_mul, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_ofNat] at hlt
  have hpos : 0 ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hIle hpos
  have hσ : 0 < ρ.re + 5 := by linarith
  have e : ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ / 2 *
      (1 / 15120 / (ρ.re + 5)) =
      ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ / (30240 * (ρ.re + 5)) := by
    field_simp
    ring
  linarith

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914: no zero of `ζ` in the open strip has
ordinate in `(15/2, 14]`; the first ordinate is `14.1347…`. Class HARD: a certified zero free
rectangle. The Euler Maclaurin formula with `N = 1` and three Bernoulli terms stops near
height `8`, S137 numerics; above that a partial sum `Σ_{n<N} n^(-s)` with certified
enclosures of `n^(-s)` is needed. -/
theorem zeta_zero_free_seven_half_fourteen (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 15 / 2 < ρ.im) : 14 < ρ.im := by
  sorry

/-- `Feed1122ZetaFourSix.zeta_zero_free_six_fourteen`, exactly its statement, from the proved
range `(6, 15/2]` and the HARD leaf on `(15/2, 14]`. -/
theorem zeta_zero_free_six_fourteen_s137 (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 6 < ρ.im) : 14 < ρ.im := by
  by_cases h7 : ρ.im ≤ 15 / 2
  · exact absurd h0 (riemannZeta_ne_zero_six_seven_half ρ hre0 hre1 him h7)
  · exact zeta_zero_free_seven_half_fourteen ρ h0 hre0 hre1 (not_le.mp h7)

end LeanLab.HelfgottMajor.Feed1122ZetaEM6

import LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoSix

/-!
# Split of `zeta_zero_free_nineteen_half_ten_half` at height `39/4`, burst 20261122 S137

`Feed1122ZetaBaseTwoSix` leaves the MEDIUM LEAF `zeta_zero_free_nineteen_half_ten_half`: no zero
of `ζ` in the open strip has ordinate in `(19/2, 21/2]`, Helfgott arXiv 1305.2897v4 Section 4.6
page 56 with Platt's verification and the first zero tables of Gram 1903 and Backlund 1914.

Same route with four Bernoulli terms from `n = 2`, Edwards 1974 Chapter 6:
`ζ(s) = 1 + 2^(-s) H₄(s) - s(s+1)⋯(s+7)/2 ∫_2^∞ (B₈({u})/20160) u^(-s-8) du`,
`H₄ = H₃ - s(s+1)⋯(s+6)/154828800`.

* PROVED `abs_B7_le`, `abs_B8_le`, `ibp6_two`, `ibp7_two`, `riemannZeta_eq_EM8_two`.
* PROVED `coeff_eight_two`, `box_eight_two_poly`, `main_eight_two_lt`, `prod_eight_two_le`.
* PROVED `riemannZeta_ne_zero_nineteen_half_thirtynine_quarter`: no zero with ordinate in `(19/2, 39/4]`.
* LEAF MEDIUM `zeta_zero_free_thirtynine_quarter_ten_half`: no zero with ordinate in `(39/4, 21/2]`.
* PROVED assembly `zeta_zero_free_nineteen_half_ten_half_s137`, exactly the statement of
  `Feed1122ZetaBaseTwoSix.zeta_zero_free_nineteen_half_ten_half`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoEight
open Complex Set MeasureTheory LeanLab.HelfgottMajor.Feed1122ZetaEM4
  LeanLab.HelfgottMajor.Feed1122ZetaEM6 LeanLab.HelfgottMajor.Feed1122ZetaBaseTwo
  LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoSix

/-- `|B₇({x})/2520| ≤ 1`, a crude bound. -/
lemma abs_B7_le (x : ℝ) : |((Int.fract x) ^ 7 - 7 / 2 * (Int.fract x) ^ 6 + 7 / 2 * (Int.fract x) ^ 5 - 7 / 6 * (Int.fract x) ^ 3 + 1 / 6 * Int.fract x) / 2520| ≤ 1 := by
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  set y := Int.fract x
  have p3 : y ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have p5 : y ^ 5 ≤ 1 := pow_le_one₀ h0 h1
  have p6 : y ^ 6 ≤ 1 := pow_le_one₀ h0 h1
  have p7 : y ^ 7 ≤ 1 := pow_le_one₀ h0 h1
  have q3 : 0 ≤ y ^ 3 := by positivity
  have q5 : 0 ≤ y ^ 5 := by positivity
  have q6 : 0 ≤ y ^ 6 := by positivity
  have q7 : 0 ≤ y ^ 7 := by positivity
  rw [abs_le]; constructor <;> linarith

/-- `|B₈({x})/20160| ≤ 1/604800`, since `B₈(y) = -1/30 + (2/3)u² + (4/3)u³ + u⁴`, `u = y(1-y)`. -/
lemma abs_B8_le (x : ℝ) : |((Int.fract x) ^ 8 - 4 * (Int.fract x) ^ 7 + 14 / 3 * (Int.fract x) ^ 6 - 7 / 3 * (Int.fract x) ^ 4 + 2 / 3 * (Int.fract x) ^ 2 - 1 / 30) / 20160| ≤ 1 / 604800 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  set y := Int.fract x
  have e : y ^ 8 - 4 * y ^ 7 + 14 / 3 * y ^ 6 - 7 / 3 * y ^ 4 + 2 / 3 * y ^ 2 - 1 / 30 =
      -1 / 30 + 2 / 3 * (y * (1 - y)) ^ 2 + 4 / 3 * (y * (1 - y)) ^ 3 + (y * (1 - y)) ^ 4 := by ring
  have hu : 0 ≤ y * (1 - y) := mul_nonneg h0 (by linarith)
  have hu' : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have u2 : (y * (1 - y)) ^ 2 ≤ 1 / 16 := by nlinarith
  have u3 : (y * (1 - y)) ^ 3 ≤ 1 / 64 := by nlinarith
  have u4 : (y * (1 - y)) ^ 4 ≤ 1 / 256 := by nlinarith
  have u2' : 0 ≤ (y * (1 - y)) ^ 2 := by positivity
  have u3' : 0 ≤ (y * (1 - y)) ^ 3 := by positivity
  have u4' : 0 ≤ (y * (1 - y)) ^ 4 := by positivity
  rw [e, abs_le]; constructor <;> linarith

/-- step six on `(2, ∞)`. -/
lemma ibp6_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 - 1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 6)) =
      (s + 6) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 7 - 7 / 2 * (Int.fract x) ^ 6 + 7 / 2 * (Int.fract x) ^ 5 - 7 / 6 * (Int.fract x) ^ 3 + 1 / 6 * Int.fract x) / 2520 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 7) := by
  have hc : Continuous fun x : ℝ => ((Int.fract x) ^ 7 - 7 / 2 * (Int.fract x) ^ 6 + 7 / 2 * (Int.fract x) ^ 5 - 7 / 6 * (Int.fract x) ^ 3 + 1 / 6 * Int.fract x) / 2520 := by
    have := ContinuousOn.comp_fract'' (f := fun y : ℝ => (y ^ 7 - 7 / 2 * y ^ 6 + 7 / 2 * y ^ 5 - 7 / 6 * y ^ 3 + 1 / 6 * y) / 2520) (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ => ((Int.fract x) ^ 7 - 7 / 2 * (Int.fract x) ^ 6 + 7 / 2 * (Int.fract x) ^ 5 - 7 / 6 * (Int.fract x) ^ 3 + 1 / 6 * Int.fract x) / 2520)
      (((Int.fract x) ^ 6 - 3 * (Int.fract x) ^ 5 + 5 / 2 * (Int.fract x) ^ 4 - 1 / 2 * (Int.fract x) ^ 2 + 1 / 42) / 360) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := (((((hf.pow 7).sub ((hf.pow 6).const_mul (7 / 2))).add ((hf.pow 5).const_mul (7 / 2))).sub
      ((hf.pow 3).const_mul (7 / 6))).add (hf.const_mul (1 / 6))).div_const 2520
    convert this using 1
    simp
    ring
  have h := ibp_gen2 hc hd (by fun_prop) (by fun_prop) abs_B7_le abs_B6_le
    (P0 := 0) (by intro n; simp) (a := -s - 6) (by simp; linarith)
  have e : (-s - 6 - 1) = -s - 7 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- step seven on `(2, ∞)`. -/
lemma ibp7_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 7 - 7 / 2 * (Int.fract x) ^ 6 + 7 / 2 * (Int.fract x) ^ 5 - 7 / 6 * (Int.fract x) ^ 3 + 1 / 6 * Int.fract x) / 2520 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 7)) =
      (1 / 604800 : ℂ) * (2 : ℂ) ^ (-s - 7) +
        (s + 7) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 8 - 4 * (Int.fract x) ^ 7 + 14 / 3 * (Int.fract x) ^ 6 - 7 / 3 * (Int.fract x) ^ 4 + 2 / 3 * (Int.fract x) ^ 2 - 1 / 30) / 20160 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 8) := by
  have hc : Continuous fun x : ℝ => ((Int.fract x) ^ 8 - 4 * (Int.fract x) ^ 7 + 14 / 3 * (Int.fract x) ^ 6 - 7 / 3 * (Int.fract x) ^ 4 + 2 / 3 * (Int.fract x) ^ 2 - 1 / 30) / 20160 := by
    have := ContinuousOn.comp_fract'' (f := fun y : ℝ => (y ^ 8 - 4 * y ^ 7 + 14 / 3 * y ^ 6 - 7 / 3 * y ^ 4 + 2 / 3 * y ^ 2 - 1 / 30) / 20160) (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ => ((Int.fract x) ^ 8 - 4 * (Int.fract x) ^ 7 + 14 / 3 * (Int.fract x) ^ 6 - 7 / 3 * (Int.fract x) ^ 4 + 2 / 3 * (Int.fract x) ^ 2 - 1 / 30) / 20160)
      (((Int.fract x) ^ 7 - 7 / 2 * (Int.fract x) ^ 6 + 7 / 2 * (Int.fract x) ^ 5 - 7 / 6 * (Int.fract x) ^ 3 + 1 / 6 * Int.fract x) / 2520) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := ((((((hf.pow 8).sub ((hf.pow 7).const_mul 4)).add ((hf.pow 6).const_mul (14 / 3))).sub
      ((hf.pow 4).const_mul (7 / 3))).add ((hf.pow 2).const_mul (2 / 3))).sub_const
      (1 / 30 : ℝ)).div_const 20160
    convert this using 1
    simp
    ring
  have h := ibp_gen2 hc hd (by fun_prop) (by fun_prop) abs_B8_le abs_B7_le
    (P0 := -1 / 604800) (by intro n; simp; norm_num) (a := -s - 7) (by simp; linarith)
  have e : (-s - 7 - 1) = -s - 8 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- Euler Maclaurin from `n = 2` with four Bernoulli terms, Edwards 1974 Chapter 6. -/
theorem riemannZeta_eq_EM8_two {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = 1 + (2 : ℂ) ^ (-s) * (1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680 - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / 154828800) -
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) / 2 *
        ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 8 - 4 * (Int.fract x) ^ 7 + 14 / 3 * (Int.fract x) ^ 6 - 7 / 3 * (Int.fract x) ^ 4 + 2 / 3 * (Int.fract x) ^ 2 - 1 / 30) / 20160 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 8) := by
  have h6 := ibp6_two hs
  have h7 := ibp7_two hs
  have p7 : (2 : ℂ) ^ (-s - 7) = (2 : ℂ) ^ (-s) / 128 := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero]
    have : (2 : ℂ) ^ (-(7 : ℂ)) = 1 / 128 := by
      rw [Complex.cpow_neg]
      norm_num
    rw [this]
    ring
  rw [p7] at h7
  rw [riemannZeta_eq_EM6_two hs h1, h6, h7]
  ring

set_option maxHeartbeats 4000000 in
/-- Certificate piece on `[361/4, 1521/16]`, proved monomial by monomial. -/
lemma coeff_eight_two (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (361 / 4 : ℝ) ≤ x) (hb : x ≤ (1521 / 16 : ℝ)) :
    0 < (-x ^ 8 - 412 * x ^ 7 - 82774 * x ^ 6 - 16069556 * x ^ 5 - 3109372129 * x ^ 4 - 432656528632 * x ^ 3 - 38199207079696 * x ^ 2 + 13692568437667584 * x - 38208902755516416) +
      (-40 * x ^ 7 - 5040 * x ^ 6 + 2326720 * x ^ 5 + 340778480 * x ^ 4 - 37549323480 * x ^ 3 - 11504386645760 * x ^ 2 + 24898326630391680 * x - 38551251379027968) * g +
      (-8 * x ^ 7 - 2860 * x ^ 6 - 45940 * x ^ 5 + 169801380 * x ^ 4 + 24631788028 * x ^ 3 + 267354427368 * x ^ 2 + 10504110667587808 * x - 33447721539062016) * g ^ 2 +
      (-280 * x ^ 6 - 23200 * x ^ 5 + 9890560 * x ^ 4 + 4139164800 * x ^ 3 + 379036372600 * x ^ 2 - 1330388947840 * x + 3685604331511680) * g ^ 3 +
      (-28 * x ^ 6 - 8508 * x ^ 5 + 631606 * x ^ 4 + 201824536 * x ^ 3 + 29901251514 * x ^ 2 + 966575656632 * x + 10630632892600304) * g ^ 4 +
      (-840 * x ^ 5 - 40400 * x ^ 4 + 14647040 * x ^ 3 - 1390299680 * x ^ 2 - 183363477640 * x + 3634029185920) * g ^ 5 +
      (-56 * x ^ 5 - 14060 * x ^ 4 + 1330344 * x ^ 3 - 159632536 * x ^ 2 - 54541152772 * x + 177383311832) * g ^ 6 +
      (-1400 * x ^ 4 - 30400 * x ^ 3 + 7864960 * x ^ 2 - 4745208320 * x - 5406581720) * g ^ 7 +
      (-70 * x ^ 4 - 13940 * x ^ 3 + 983606 * x ^ 2 - 165185380 * x + 2753015071) * g ^ 8 +
      (-1400 * x ^ 3 - 5200 * x ^ 2 - 282560 * x + 443477680) * g ^ 9 +
      (-56 * x ^ 3 - 8292 * x ^ 2 + 235660 * x + 10400756) * g ^ 10 +
      (-840 * x ^ 2 + 4960 * x - 1064320) * g ^ 11 +
      (-28 * x ^ 2 - 2740 * x - 12374) * g ^ 12 +
      (-280 * x + 2000) * g ^ 13 +
      (-8 * x - 388) * g ^ 14 +
      (-40) * g ^ 15 +
      (-1) * g ^ 16 := by
  have hx : 0 ≤ x := by linarith
  have u1 : x ^ 1 ≤ (1521 / 16 : ℝ) := by
    calc x ^ 1 ≤ (1521 / 16 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (361 / 4 : ℝ) ≤ x ^ 1 := by
    calc (361 / 4 : ℝ) = (361 / 4 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (2313441 / 256 : ℝ) := by
    calc x ^ 2 ≤ (1521 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (130321 / 16 : ℝ) ≤ x ^ 2 := by
    calc (130321 / 16 : ℝ) = (361 / 4 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (3518743761 / 4096 : ℝ) := by
    calc x ^ 3 ≤ (1521 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (47045881 / 64 : ℝ) ≤ x ^ 3 := by
    calc (47045881 / 64 : ℝ) = (361 / 4 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (5352009260481 / 65536 : ℝ) := by
    calc x ^ 4 ≤ (1521 / 16 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (16983563041 / 256 : ℝ) ≤ x ^ 4 := by
    calc (16983563041 / 256 : ℝ) = (361 / 4 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (8140406085191601 / 1048576 : ℝ) := by
    calc x ^ 5 ≤ (1521 / 16 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (6131066257801 / 1024 : ℝ) ≤ x ^ 5 := by
    calc (6131066257801 / 1024 : ℝ) = (361 / 4 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (12381557655576425121 / 16777216 : ℝ) := by
    calc x ^ 6 ≤ (1521 / 16 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (2213314919066161 / 4096 : ℝ) ≤ x ^ 6 := by
    calc (2213314919066161 / 4096 : ℝ) = (361 / 4 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (18832349194131742609041 / 268435456 : ℝ) := by
    calc x ^ 7 ≤ (1521 / 16 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (799006685782884121 / 16384 : ℝ) ≤ x ^ 7 := by
    calc (799006685782884121 / 16384 : ℝ) = (361 / 4 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have u8 : x ^ 8 ≤ (28644003124274380508351361 / 4294967296 : ℝ) := by
    calc x ^ 8 ≤ (1521 / 16 : ℝ) ^ 8 := pow_le_pow_left₀ hx hb 8
      _ = _ := by norm_num
  have l8 : (288441413567621167681 / 65536 : ℝ) ≤ x ^ 8 := by
    calc (288441413567621167681 / 65536 : ℝ) = (361 / 4 : ℝ) ^ 8 := by norm_num
      _ ≤ x ^ 8 := pow_le_pow_left₀ (by norm_num) ha 8
  have hc0 : (5321586687188742 : ℝ) ≤ -x ^ 8 - 412 * x ^ 7 - 82774 * x ^ 6 - 16069556 * x ^ 5 - 3109372129 * x ^ 4 - 432656528632 * x ^ 3 - 38199207079696 * x ^ 2 + 13692568437667584 * x - 38208902755516416 := by linarith
  have hc1 : (2102314666836030171 : ℝ) ≤ -40 * x ^ 7 - 5040 * x ^ 6 + 2326720 * x ^ 5 + 340778480 * x ^ 4 - 37549323480 * x ^ 3 - 11504386645760 * x ^ 2 + 24898326630391680 * x - 38551251379027968 := by linarith
  have t1 : 0 ≤ (-40 * x ^ 7 - 5040 * x ^ 6 + 2326720 * x ^ 5 + 340778480 * x ^ 4 - 37549323480 * x ^ 3 - 11504386645760 * x ^ 2 + 24898326630391680 * x - 38551251379027968) * g := mul_nonneg (by linarith) (by positivity)
  have hc2 : (943068913998699448 : ℝ) ≤ -8 * x ^ 7 - 2860 * x ^ 6 - 45940 * x ^ 5 + 169801380 * x ^ 4 + 24631788028 * x ^ 3 + 267354427368 * x ^ 2 + 10504110667587808 * x - 33447721539062016 := by linarith
  have t2 : 0 ≤ (-8 * x ^ 7 - 2860 * x ^ 6 - 45940 * x ^ 5 + 169801380 * x ^ 4 + 24631788028 * x ^ 3 + 267354427368 * x ^ 2 + 10504110667587808 * x - 33447721539062016) * g ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hc3 : (9958487604417256 : ℝ) ≤ -280 * x ^ 6 - 23200 * x ^ 5 + 9890560 * x ^ 4 + 4139164800 * x ^ 3 + 379036372600 * x ^ 2 - 1330388947840 * x + 3685604331511680 := by linarith
  have t3 : 0 ≤ (-280 * x ^ 6 - 23200 * x ^ 5 + 9890560 * x ^ 4 + 4139164800 * x ^ 3 + 379036372600 * x ^ 2 - 1330388947840 * x + 3685604331511680) * g ^ 3 := mul_nonneg (by linarith) (by positivity)
  have hc4 : (11064961442430709 : ℝ) ≤ -28 * x ^ 6 - 8508 * x ^ 5 + 631606 * x ^ 4 + 201824536 * x ^ 3 + 29901251514 * x ^ 2 + 966575656632 * x + 10630632892600304 := by linarith
  have t4 : 0 ≤ (-28 * x ^ 6 - 8508 * x ^ 5 + 631606 * x ^ 4 + 201824536 * x ^ 3 + 29901251514 * x ^ 2 + 966575656632 * x + 10630632892600304) * g ^ 4 := mul_nonneg (by linarith) (by positivity)
  have hc5 : (-25414453035121 : ℝ) ≤ -840 * x ^ 5 - 40400 * x ^ 4 + 14647040 * x ^ 3 - 1390299680 * x ^ 2 - 183363477640 * x + 3634029185920 := by linarith
  have t5 : (-25414453035121 : ℝ) ≤ (-840 * x ^ 5 - 40400 * x ^ 4 + 14647040 * x ^ 3 - 1390299680 * x ^ 2 - 183363477640 * x + 3634029185920) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-7055046858373 : ℝ) ≤ -56 * x ^ 5 - 14060 * x ^ 4 + 1330344 * x ^ 3 - 159632536 * x ^ 2 - 54541152772 * x + 177383311832 := by linarith
  have t6 : (-7055046858373 : ℝ) ≤ (-56 * x ^ 5 - 14060 * x ^ 4 + 1330344 * x ^ 3 - 159632536 * x ^ 2 - 54541152772 * x + 177383311832) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-532884285744 : ℝ) ≤ -1400 * x ^ 4 - 30400 * x ^ 3 + 7864960 * x ^ 2 - 4745208320 * x - 5406581720 := by linarith
  have t7 : (-532884285744 : ℝ) ≤ (-1400 * x ^ 4 - 30400 * x ^ 3 + 7864960 * x ^ 2 - 4745208320 * x - 5406581720) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-22630362512 : ℝ) ≤ -70 * x ^ 4 - 13940 * x ^ 3 + 983606 * x ^ 2 - 165185380 * x + 2753015071 := by linarith
  have t8 : (-22630362512 : ℝ) ≤ (-70 * x ^ 4 - 13940 * x ^ 3 + 983606 * x ^ 2 - 165185380 * x + 2753015071) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-833070572 : ℝ) ≤ -1400 * x ^ 3 - 5200 * x ^ 2 - 282560 * x + 443477680 := by linarith
  have t9 : (-833070572 : ℝ) ≤ (-1400 * x ^ 3 - 5200 * x ^ 2 - 282560 * x + 443477680) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-91372554 : ℝ) ≤ -56 * x ^ 3 - 8292 * x ^ 2 + 235660 * x + 10400756 := by linarith
  have t10 : (-91372554 : ℝ) ≤ (-56 * x ^ 3 - 8292 * x ^ 2 + 235660 * x + 10400756) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-8207659 : ℝ) ≤ -840 * x ^ 2 + 4960 * x - 1064320 := by linarith
  have t11 : (-8207659 : ℝ) ≤ (-840 * x ^ 2 + 4960 * x - 1064320) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-525878 : ℝ) ≤ -28 * x ^ 2 - 2740 * x - 12374 := by linarith
  have t12 : (-525878 : ℝ) ≤ (-28 * x ^ 2 - 2740 * x - 12374) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  have hc13 : (-24618 : ℝ) ≤ -280 * x + 2000 := by linarith
  have t13 : (-24618 : ℝ) ≤ (-280 * x + 2000) * g ^ 13 := by
    have g0 : 0 ≤ g ^ 13 := by positivity
    have g1 : g ^ 13 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc13) g0]
  have hc14 : (-1149 : ℝ) ≤ -8 * x - 388 := by linarith
  have t14 : (-1149 : ℝ) ≤ (-8 * x - 388) * g ^ 14 := by
    have g0 : 0 ≤ g ^ 14 := by positivity
    have g1 : g ^ 14 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc14) g0]
  have hc15 : (-40 : ℝ) ≤ -40 := by norm_num
  have t15 : (-40 : ℝ) ≤ (-40) * g ^ 15 := by
    have g0 : 0 ≤ g ^ 15 := by positivity
    have g1 : g ^ 15 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc15) g0]
  have hc16 : (-1 : ℝ) ≤ -1 := by norm_num
  have t16 : (-1 : ℝ) ≤ (-1) * g ^ 16 := by
    have g0 : 0 ≤ g ^ 16 := by positivity
    have g1 : g ^ 16 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc16) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- The box polynomial for `H₄ = N₄ / (154828800 (s - 1))`, proved. -/
lemma box_eight_two_poly (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht0 : 19 / 2 ≤ t) (ht1 : t ≤ 39 / 4) :
    ((-σ ^ 8 - 20 * σ ^ 7 + 28 * σ ^ 6 * t ^ 2 + 6 * σ ^ 6 + 420 * σ ^ 5 * t ^ 2 + 880 * σ ^ 5 - 70 * σ ^ 4 * t ^ 4 - 90 * σ ^ 4 * t ^ 2 - 23769 * σ ^ 4 - 700 * σ ^ 3 * t ^ 4 - 8800 * σ ^ 3 * t ^ 2 - 51500 * σ ^ 3 + 28 * σ ^ 2 * t ^ 6 + 90 * σ ^ 2 * t ^ 4 + 142614 * σ ^ 2 * t ^ 2 + 6474964 * σ ^ 2 + 140 * σ * t ^ 6 + 4400 * σ * t ^ 4 + 154500 * σ * t ^ 2 + 71013840 * σ - t ^ 8 - 6 * t ^ 6 - 23769 * t ^ 4 - 6474964 * t ^ 2 + 232243200) ^ 2 + (4 * t * (-2 * σ ^ 7 - 35 * σ ^ 6 + 14 * σ ^ 5 * t ^ 2 + 9 * σ ^ 5 + 175 * σ ^ 4 * t ^ 2 + 1100 * σ ^ 4 - 14 * σ ^ 3 * t ^ 4 - 30 * σ ^ 3 * t ^ 2 - 23769 * σ ^ 3 - 105 * σ ^ 2 * t ^ 4 - 2200 * σ ^ 2 * t ^ 2 - 38625 * σ ^ 2 + 2 * σ * t ^ 6 + 9 * σ * t ^ 4 + 23769 * σ * t ^ 2 + 3237482 * σ + 5 * t ^ 6 + 220 * t ^ 4 + 12875 * t ^ 2 + 17753460)) ^ 2) <
      (81 / 100 + 2 * σ / 3) ^ 2 * 154828800 ^ 2 * ((σ - 1) ^ 2 + t ^ 2) := by
  have hx0 : 361 / 4 ≤ t ^ 2 := by nlinarith
  have hx1 : t ^ 2 ≤ 1521 / 16 := by nlinarith
  have h := coeff_eight_two σ (t ^ 2) h0 h1 hx0 hx1
  have e : (81 / 100 + 2 * σ / 3) ^ 2 * 154828800 ^ 2 * ((σ - 1) ^ 2 + t ^ 2) -
      ((-σ ^ 8 - 20 * σ ^ 7 + 28 * σ ^ 6 * t ^ 2 + 6 * σ ^ 6 + 420 * σ ^ 5 * t ^ 2 + 880 * σ ^ 5 - 70 * σ ^ 4 * t ^ 4 - 90 * σ ^ 4 * t ^ 2 - 23769 * σ ^ 4 - 700 * σ ^ 3 * t ^ 4 - 8800 * σ ^ 3 * t ^ 2 - 51500 * σ ^ 3 + 28 * σ ^ 2 * t ^ 6 + 90 * σ ^ 2 * t ^ 4 + 142614 * σ ^ 2 * t ^ 2 + 6474964 * σ ^ 2 + 140 * σ * t ^ 6 + 4400 * σ * t ^ 4 + 154500 * σ * t ^ 2 + 71013840 * σ - t ^ 8 - 6 * t ^ 6 - 23769 * t ^ 4 - 6474964 * t ^ 2 + 232243200) ^ 2 + (4 * t * (-2 * σ ^ 7 - 35 * σ ^ 6 + 14 * σ ^ 5 * t ^ 2 + 9 * σ ^ 5 + 175 * σ ^ 4 * t ^ 2 + 1100 * σ ^ 4 - 14 * σ ^ 3 * t ^ 4 - 30 * σ ^ 3 * t ^ 2 - 23769 * σ ^ 3 - 105 * σ ^ 2 * t ^ 4 - 2200 * σ ^ 2 * t ^ 2 - 38625 * σ ^ 2 + 2 * σ * t ^ 6 + 9 * σ * t ^ 4 + 23769 * σ * t ^ 2 + 3237482 * σ + 5 * t ^ 6 + 220 * t ^ 4 + 12875 * t ^ 2 + 17753460)) ^ 2) =
      (-(t ^ 2) ^ 8 - 412 * (t ^ 2) ^ 7 - 82774 * (t ^ 2) ^ 6 - 16069556 * (t ^ 2) ^ 5 - 3109372129 * (t ^ 2) ^ 4 - 432656528632 * (t ^ 2) ^ 3 - 38199207079696 * (t ^ 2) ^ 2 + 13692568437667584 * t ^ 2 - 38208902755516416) +
      (-40 * (t ^ 2) ^ 7 - 5040 * (t ^ 2) ^ 6 + 2326720 * (t ^ 2) ^ 5 + 340778480 * (t ^ 2) ^ 4 - 37549323480 * (t ^ 2) ^ 3 - 11504386645760 * (t ^ 2) ^ 2 + 24898326630391680 * t ^ 2 - 38551251379027968) * σ +
      (-8 * (t ^ 2) ^ 7 - 2860 * (t ^ 2) ^ 6 - 45940 * (t ^ 2) ^ 5 + 169801380 * (t ^ 2) ^ 4 + 24631788028 * (t ^ 2) ^ 3 + 267354427368 * (t ^ 2) ^ 2 + 10504110667587808 * t ^ 2 - 33447721539062016) * σ ^ 2 +
      (-280 * (t ^ 2) ^ 6 - 23200 * (t ^ 2) ^ 5 + 9890560 * (t ^ 2) ^ 4 + 4139164800 * (t ^ 2) ^ 3 + 379036372600 * (t ^ 2) ^ 2 - 1330388947840 * t ^ 2 + 3685604331511680) * σ ^ 3 +
      (-28 * (t ^ 2) ^ 6 - 8508 * (t ^ 2) ^ 5 + 631606 * (t ^ 2) ^ 4 + 201824536 * (t ^ 2) ^ 3 + 29901251514 * (t ^ 2) ^ 2 + 966575656632 * t ^ 2 + 10630632892600304) * σ ^ 4 +
      (-840 * (t ^ 2) ^ 5 - 40400 * (t ^ 2) ^ 4 + 14647040 * (t ^ 2) ^ 3 - 1390299680 * (t ^ 2) ^ 2 - 183363477640 * t ^ 2 + 3634029185920) * σ ^ 5 +
      (-56 * (t ^ 2) ^ 5 - 14060 * (t ^ 2) ^ 4 + 1330344 * (t ^ 2) ^ 3 - 159632536 * (t ^ 2) ^ 2 - 54541152772 * t ^ 2 + 177383311832) * σ ^ 6 +
      (-1400 * (t ^ 2) ^ 4 - 30400 * (t ^ 2) ^ 3 + 7864960 * (t ^ 2) ^ 2 - 4745208320 * t ^ 2 - 5406581720) * σ ^ 7 +
      (-70 * (t ^ 2) ^ 4 - 13940 * (t ^ 2) ^ 3 + 983606 * (t ^ 2) ^ 2 - 165185380 * t ^ 2 + 2753015071) * σ ^ 8 +
      (-1400 * (t ^ 2) ^ 3 - 5200 * (t ^ 2) ^ 2 - 282560 * t ^ 2 + 443477680) * σ ^ 9 +
      (-56 * (t ^ 2) ^ 3 - 8292 * (t ^ 2) ^ 2 + 235660 * t ^ 2 + 10400756) * σ ^ 10 +
      (-840 * (t ^ 2) ^ 2 + 4960 * t ^ 2 - 1064320) * σ ^ 11 +
      (-28 * (t ^ 2) ^ 2 - 2740 * t ^ 2 - 12374) * σ ^ 12 +
      (-280 * t ^ 2 + 2000) * σ ^ 13 +
      (-8 * t ^ 2 - 388) * σ ^ 14 +
      (-40) * σ ^ 15 +
      (-1) * σ ^ 16 := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- The main term is small: `‖H₄(s)‖ < 81/100 + 2σ/3` on `(0,1) × (19/2, 39/4]`. Proved. -/
lemma main_eight_two_lt (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 19 / 2 < s.im)
    (ht1 : s.im ≤ 39 / 4) :
    ‖1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680 - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / 154828800‖ < 81 / 100 + 2 * s.re / 3 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hM : 1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680 - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / 154828800 = (160 * (483840 * (s - 1) + 1935360 + 40320 * s * (s - 1) - 168 * (s - 1) * s * (s + 1) * (s + 2) + (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) - (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) / (154828800 * (s - 1)) := by
    field_simp
    ring
  rw [hM, norm_div, norm_mul, Complex.norm_ofNat]
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  rw [div_lt_iff₀ (by positivity)]
  set P : ℂ := 160 * (483840 * (s - 1) + 1935360 + 40320 * s * (s - 1) - 168 * (s - 1) * s * (s + 1) * (s + 2) + (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) - (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) with hP
  have hPre : P.re = -s.re ^ 8 - 20 * s.re ^ 7 + 28 * s.re ^ 6 * s.im ^ 2 + 6 * s.re ^ 6 + 420 * s.re ^ 5 * s.im ^ 2 + 880 * s.re ^ 5 - 70 * s.re ^ 4 * s.im ^ 4 - 90 * s.re ^ 4 * s.im ^ 2 - 23769 * s.re ^ 4 - 700 * s.re ^ 3 * s.im ^ 4 - 8800 * s.re ^ 3 * s.im ^ 2 - 51500 * s.re ^ 3 + 28 * s.re ^ 2 * s.im ^ 6 + 90 * s.re ^ 2 * s.im ^ 4 + 142614 * s.re ^ 2 * s.im ^ 2 + 6474964 * s.re ^ 2 + 140 * s.re * s.im ^ 6 + 4400 * s.re * s.im ^ 4 + 154500 * s.re * s.im ^ 2 + 71013840 * s.re - s.im ^ 8 - 6 * s.im ^ 6 - 23769 * s.im ^ 4 - 6474964 * s.im ^ 2 + 232243200 := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hPim : P.im = 4 * s.im * (-2 * s.re ^ 7 - 35 * s.re ^ 6 + 14 * s.re ^ 5 * s.im ^ 2 + 9 * s.re ^ 5 + 175 * s.re ^ 4 * s.im ^ 2 + 1100 * s.re ^ 4 - 14 * s.re ^ 3 * s.im ^ 4 - 30 * s.re ^ 3 * s.im ^ 2 - 23769 * s.re ^ 3 - 105 * s.re ^ 2 * s.im ^ 4 - 2200 * s.re ^ 2 * s.im ^ 2 - 38625 * s.re ^ 2 + 2 * s.re * s.im ^ 6 + 9 * s.re * s.im ^ 4 + 23769 * s.re * s.im ^ 2 + 3237482 * s.re + 5 * s.im ^ 6 + 220 * s.im ^ 4 + 12875 * s.im ^ 2 + 17753460) := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hc : 0 < (81 / 100 + 2 * s.re / 3) * (154828800 * ‖s - 1‖) := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 hc.le
  have e1 : ((81 / 100 + 2 * s.re / 3) * (154828800 * ‖s - 1‖)) ^ 2 =
      (81 / 100 + 2 * s.re / 3) ^ 2 * 154828800 ^ 2 * ((s.re - 1) ^ 2 + s.im ^ 2) := by
    rw [mul_pow, mul_pow, hsq (s - 1)]
    simp
    ring
  rw [e1, hsq P, hPre, hPim]
  exact box_eight_two_poly s.re s.im h0.le h1.le ht0.le ht1

/-- The remainder factor: `‖s‖ ⋯ ‖s+7‖ ≤ 199142854` on the box. Proved. -/
lemma prod_eight_two_le (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 19 / 2 < s.im)
    (ht1 : s.im ≤ 39 / 4) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ * ‖s + 7‖ ≤ 199142854 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have ht2 : s.im ^ 2 ≤ 1521 / 16 := by nlinarith
  have n0 : ‖s‖ ^ 2 ≤ 1537 / 16 := by
    rw [hsq]; nlinarith
  have n1 : ‖s + 1‖ ^ 2 ≤ 1585 / 16 := by
    rw [hsq]; simp only [add_re, one_re, add_im, one_im]; nlinarith
  have n2 : ‖s + 2‖ ^ 2 ≤ 1665 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n3 : ‖s + 3‖ ^ 2 ≤ 1777 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n4 : ‖s + 4‖ ^ 2 ≤ 1921 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n5 : ‖s + 5‖ ^ 2 ≤ 2097 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n6 : ‖s + 6‖ ^ 2 ≤ 2305 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n7 : ‖s + 7‖ ^ 2 ≤ 2545 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have hsq' : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ * ‖s + 7‖) ^ 2 ≤ (1537 / 16) * (1585 / 16) * (1665 / 16) * (1777 / 16) * (1921 / 16) * (2097 / 16) * (2305 / 16) * (2545 / 16) := by
    have e : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ * ‖s + 7‖) ^ 2 = ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 * ‖s + 4‖ ^ 2 * ‖s + 5‖ ^ 2 * ‖s + 6‖ ^ 2 * ‖s + 7‖ ^ 2 := by ring
    rw [e]
    have q1 := mul_le_mul n0 n1 (by positivity) (by norm_num)
    have q2 := mul_le_mul q1 n2 (by positivity) (by norm_num)
    have q3 := mul_le_mul q2 n3 (by positivity) (by norm_num)
    have q4 := mul_le_mul q3 n4 (by positivity) (by norm_num)
    have q5 := mul_le_mul q4 n5 (by positivity) (by norm_num)
    have q6 := mul_le_mul q5 n6 (by positivity) (by norm_num)
    exact mul_le_mul q6 n7 (by positivity) (by norm_num)
  have : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ * ‖s + 7‖) ^ 2 ≤ 199142854 ^ 2 := by
    refine hsq'.trans ?_; norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).mp this

/-- PROVED: `ζ` has no zero with `0 < Re ρ < 1` and `19/2 < Im ρ ≤ 39/4`, same argument as
`riemannZeta_ne_zero_seventeen_half_nineteen_half` with the four term formula. -/
theorem riemannZeta_ne_zero_nineteen_half_thirtynine_quarter (ρ : ℂ) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (ht0 : 19 / 2 < ρ.im) (ht1 : ρ.im ≤ 39 / 4) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM8_two h0 hρ1
  set I := ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 8 - 4 * (Int.fract x) ^ 7 + 14 / 3 * (Int.fract x) ^ 6 - 7 / 3 * (Int.fract x) ^ 4 + 2 / 3 * (Int.fract x) ^ 2 - 1 / 30) / 20160 : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 8) with hI
  set H := 1 / 2 + 2 / (ρ - 1) + ρ / 24 - ρ * (ρ + 1) * (ρ + 2) / 5760 + ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) / 967680 - ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) * (ρ + 6) / 154828800 with hH
  set Q := ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) * (ρ + 6) * (ρ + 7) / 2 * I with hQ
  have hkey : (2 : ℂ) ^ (-ρ) * H = Q - 1 := by
    rw [hz] at hEM; linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / 604800 * (2 : ℝ) ^ ((-ρ - 8).re + 1) / (-(-ρ - 8).re - 1) :=
    norm_weight_int_le2 (by fun_prop) abs_B8_le (by simp; linarith)
  have hre1 : (-ρ - 8).re + 1 = -ρ.re - 7 := by simp; ring
  have hre2 : (-(-ρ - 8).re - 1) = ρ.re + 7 := by simp; ring
  rw [hre1, hre2] at hIle
  have hn2 : ‖(2 : ℂ) ^ (-ρ)‖ = (2 : ℝ) ^ (-ρ.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (-ρ)
    simpa using this
  have hP := prod_eight_two_le ρ h0 h1 ht0 ht1
  have hσ : 0 < ρ.re + 7 := by linarith
  have hQle : ‖Q‖ ≤ 199142854 / 2 * (1 / 604800 * (2 : ℝ) ^ (-ρ.re - 7) / (ρ.re + 7)) := by
    rw [hQ, norm_mul, norm_div, Complex.norm_ofNat, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_mul, norm_mul, norm_mul]
    have hIn : 0 ≤ ‖I‖ := norm_nonneg _
    calc ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ * ‖ρ + 6‖ * ‖ρ + 7‖ / 2 * ‖I‖
        ≤ 199142854 / 2 * ‖I‖ := by
          apply mul_le_mul_of_nonneg_right _ hIn; linarith
      _ ≤ 199142854 / 2 * (1 / 604800 * (2 : ℝ) ^ (-ρ.re - 7) / (ρ.re + 7)) :=
          mul_le_mul_of_nonneg_left hIle (by norm_num)
  have hsplit : (2 : ℝ) ^ (-ρ.re - 7) = (2 : ℝ) ^ (-ρ.re) / 128 := by
    rw [sub_eq_add_neg, Real.rpow_add two_pos]
    rw [show (-(7 : ℝ)) = ((-7 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
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
  have hE : (2 : ℝ) ^ ρ.re * ‖Q‖ ≤ 19 / 100 := by
    have := mul_le_mul_of_nonneg_left hQle hupos.le
    rw [hsplit] at this
    have e : (2 : ℝ) ^ ρ.re * (199142854 / 2 * (1 / 604800 * ((2 : ℝ) ^ (-ρ.re) / 128) / (ρ.re + 7))) =
        199142854 / 154828800 / (ρ.re + 7) * ((2 : ℝ) ^ ρ.re * (2 : ℝ) ^ (-ρ.re)) := by
      field_simp
      ring
    rw [e, hu, mul_one] at this
    have : 199142854 / 154828800 / (ρ.re + 7) ≤ 19 / 100 := by
      rw [div_le_iff₀ hσ]; nlinarith
    linarith
  have hH2 : (2 : ℝ) ^ ρ.re - 19 / 100 ≤ ‖H‖ := by
    have := mul_le_mul_of_nonneg_left hlow hupos.le
    have e : (2 : ℝ) ^ ρ.re * ((2 : ℝ) ^ (-ρ.re) * ‖H‖) = ‖H‖ := by
      rw [← mul_assoc, hu, one_mul]
    rw [e, mul_sub, mul_one] at this
    linarith
  have hlo := two_rpow_ge ρ.re h0.le
  have hup := main_eight_two_lt ρ h0 h1 ht0 ht1
  rw [← hH] at hup
  linarith

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914, read on the window `(39/4, 21/2]`: no zero
of `ζ` in the open strip has ordinate in `(39/4, 21/2]`. Class MEDIUM: the route of this file with
five or six Bernoulli terms; with the crude constant error bound of this file six terms reach
about `41/4` only, so the last piece needs the exact error, S137 numerics. -/
theorem zeta_zero_free_thirtynine_quarter_ten_half (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : 39 / 4 < ρ.im) : 21 / 2 < ρ.im := by
  sorry

/-- `Feed1122ZetaBaseTwoSix.zeta_zero_free_nineteen_half_ten_half`, exactly its statement, from the
proved range `(19/2, 39/4]` and the MEDIUM leaf on `(39/4, 21/2]`. -/
theorem zeta_zero_free_nineteen_half_ten_half_s137 (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : 19 / 2 < ρ.im) : 21 / 2 < ρ.im := by
  by_cases h : ρ.im ≤ 39 / 4
  · exact absurd h0 (riemannZeta_ne_zero_nineteen_half_thirtynine_quarter ρ hre0 hre1 him h)
  · exact zeta_zero_free_thirtynine_quarter_ten_half ρ h0 hre0 hre1 (not_le.mp h)

end LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoEight

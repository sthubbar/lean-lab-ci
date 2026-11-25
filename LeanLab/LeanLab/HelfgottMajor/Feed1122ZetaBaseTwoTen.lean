import LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoEight

/-!
# Split of `zeta_zero_free_thirtynine_quarter_ten_half` at height `10`, burst 20261122 S137

`Feed1122ZetaBaseTwoEight` leaves the MEDIUM LEAF `zeta_zero_free_thirtynine_quarter_ten_half`:
no zero of `ζ` in the open strip has ordinate in `(39/4, 21/2]`, Helfgott arXiv 1305.2897v4
Section 4.6 page 56 with Platt's verification and the first zero tables of Gram 1903 and
Backlund 1914.

Same route with five Bernoulli terms from `n = 2`, Edwards 1974 Chapter 6.

* PROVED `abs_B9_le`, `abs_B10_le`, `ibp8_two`, `ibp9_two`, `riemannZeta_eq_EM10_two`.
* PROVED `coeff_ten_lo`, `coeff_ten_hi`, `box_ten_two_poly`, `main_ten_two_lt`, `prod_ten_two_le`.
* PROVED `riemannZeta_ne_zero_thirtynine_quarter_ten`: no zero with ordinate in `(39/4, 10]`.
* LEAF MEDIUM `zeta_zero_free_ten_ten_half`: no zero with ordinate in `(10, 21/2]`.
* PROVED assembly `zeta_zero_free_thirtynine_quarter_ten_half_s137`, exactly the statement of
  `Feed1122ZetaBaseTwoEight.zeta_zero_free_thirtynine_quarter_ten_half`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoTen
open Complex Set MeasureTheory LeanLab.HelfgottMajor.Feed1122ZetaEM4
  LeanLab.HelfgottMajor.Feed1122ZetaEM6 LeanLab.HelfgottMajor.Feed1122ZetaBaseTwo
  LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoSix LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoEight

/-- `|B₉({x})/181440| ≤ 1`, a crude bound. -/
lemma abs_B9_le (x : ℝ) : |((Int.fract x) ^ 9 - 9 / 2 * (Int.fract x) ^ 8 + 6 * (Int.fract x) ^ 7 - 21 / 5 * (Int.fract x) ^ 5 + 2 * (Int.fract x) ^ 3 - 3 / 10 * Int.fract x) / 181440| ≤ 1 := by
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  set y := Int.fract x
  have p3 : y ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have p5 : y ^ 5 ≤ 1 := pow_le_one₀ h0 h1
  have p7 : y ^ 7 ≤ 1 := pow_le_one₀ h0 h1
  have p8 : y ^ 8 ≤ 1 := pow_le_one₀ h0 h1
  have p9 : y ^ 9 ≤ 1 := pow_le_one₀ h0 h1
  have q3 : 0 ≤ y ^ 3 := by positivity
  have q5 : 0 ≤ y ^ 5 := by positivity
  have q7 : 0 ≤ y ^ 7 := by positivity
  have q8 : 0 ≤ y ^ 8 := by positivity
  have q9 : 0 ≤ y ^ 9 := by positivity
  rw [abs_le]; constructor <;> linarith

/-- `|B₁₀({x})/1814400| ≤ 1/23950080`, since
`B₁₀(y) = 5/66 - (3/2)u² - 3u³ - (5/2)u⁴ - u⁵`, `u = y(1-y)`. -/
lemma abs_B10_le (x : ℝ) : |((Int.fract x) ^ 10 - 5 * (Int.fract x) ^ 9 + 15 / 2 * (Int.fract x) ^ 8 - 7 * (Int.fract x) ^ 6 + 5 * (Int.fract x) ^ 4 - 3 / 2 * (Int.fract x) ^ 2 + 5 / 66) / 1814400| ≤ 1 / 23950080 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  set y := Int.fract x
  have e : y ^ 10 - 5 * y ^ 9 + 15 / 2 * y ^ 8 - 7 * y ^ 6 + 5 * y ^ 4 - 3 / 2 * y ^ 2 + 5 / 66 =
      5 / 66 - 3 / 2 * (y * (1 - y)) ^ 2 - 3 * (y * (1 - y)) ^ 3 - 5 / 2 * (y * (1 - y)) ^ 4 -
        (y * (1 - y)) ^ 5 := by ring
  have hu : 0 ≤ y * (1 - y) := mul_nonneg h0 (by linarith)
  have hu' : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have u2 : (y * (1 - y)) ^ 2 ≤ 1 / 16 := by nlinarith
  have u3 : (y * (1 - y)) ^ 3 ≤ 1 / 64 := by nlinarith
  have u4 : (y * (1 - y)) ^ 4 ≤ 1 / 256 := by nlinarith
  have u5 : (y * (1 - y)) ^ 5 ≤ 1 / 1024 := by nlinarith
  have u2' : 0 ≤ (y * (1 - y)) ^ 2 := by positivity
  have u3' : 0 ≤ (y * (1 - y)) ^ 3 := by positivity
  have u4' : 0 ≤ (y * (1 - y)) ^ 4 := by positivity
  have u5' : 0 ≤ (y * (1 - y)) ^ 5 := by positivity
  rw [e, abs_le]; constructor <;> linarith

/-- step eight on `(2, ∞)`. -/
lemma ibp8_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 8 - 4 * (Int.fract x) ^ 7 + 14 / 3 * (Int.fract x) ^ 6 - 7 / 3 * (Int.fract x) ^ 4 + 2 / 3 * (Int.fract x) ^ 2 - 1 / 30) / 20160 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 8)) =
      (s + 8) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 9 - 9 / 2 * (Int.fract x) ^ 8 + 6 * (Int.fract x) ^ 7 - 21 / 5 * (Int.fract x) ^ 5 + 2 * (Int.fract x) ^ 3 - 3 / 10 * Int.fract x) / 181440 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 9) := by
  have hc : Continuous fun x : ℝ => ((Int.fract x) ^ 9 - 9 / 2 * (Int.fract x) ^ 8 + 6 * (Int.fract x) ^ 7 - 21 / 5 * (Int.fract x) ^ 5 + 2 * (Int.fract x) ^ 3 - 3 / 10 * Int.fract x) / 181440 := by
    have := ContinuousOn.comp_fract'' (f := fun y : ℝ => (y ^ 9 - 9 / 2 * y ^ 8 + 6 * y ^ 7 - 21 / 5 * y ^ 5 + 2 * y ^ 3 - 3 / 10 * y) / 181440) (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ => ((Int.fract x) ^ 9 - 9 / 2 * (Int.fract x) ^ 8 + 6 * (Int.fract x) ^ 7 - 21 / 5 * (Int.fract x) ^ 5 + 2 * (Int.fract x) ^ 3 - 3 / 10 * Int.fract x) / 181440)
      (((Int.fract x) ^ 8 - 4 * (Int.fract x) ^ 7 + 14 / 3 * (Int.fract x) ^ 6 - 7 / 3 * (Int.fract x) ^ 4 + 2 / 3 * (Int.fract x) ^ 2 - 1 / 30) / 20160) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := ((((((hf.pow 9).sub ((hf.pow 8).const_mul (9 / 2))).add ((hf.pow 7).const_mul 6)).sub
      ((hf.pow 5).const_mul (21 / 5))).add ((hf.pow 3).const_mul 2)).sub
      (hf.const_mul (3 / 10))).div_const 181440
    convert this using 1
    simp
    ring
  have h := ibp_gen2 hc hd (by fun_prop) (by fun_prop) abs_B9_le abs_B8_le
    (P0 := 0) (by intro n; simp) (a := -s - 8) (by simp; linarith)
  have e : (-s - 8 - 1) = -s - 9 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- step nine on `(2, ∞)`. -/
lemma ibp9_two {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 9 - 9 / 2 * (Int.fract x) ^ 8 + 6 * (Int.fract x) ^ 7 - 21 / 5 * (Int.fract x) ^ 5 + 2 * (Int.fract x) ^ 3 - 3 / 10 * Int.fract x) / 181440 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 9)) =
      -(1 / 23950080 : ℂ) * (2 : ℂ) ^ (-s - 9) +
        (s + 9) * ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 10 - 5 * (Int.fract x) ^ 9 + 15 / 2 * (Int.fract x) ^ 8 - 7 * (Int.fract x) ^ 6 + 5 * (Int.fract x) ^ 4 - 3 / 2 * (Int.fract x) ^ 2 + 5 / 66) / 1814400 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 10) := by
  have hc : Continuous fun x : ℝ => ((Int.fract x) ^ 10 - 5 * (Int.fract x) ^ 9 + 15 / 2 * (Int.fract x) ^ 8 - 7 * (Int.fract x) ^ 6 + 5 * (Int.fract x) ^ 4 - 3 / 2 * (Int.fract x) ^ 2 + 5 / 66) / 1814400 := by
    have := ContinuousOn.comp_fract'' (f := fun y : ℝ => (y ^ 10 - 5 * y ^ 9 + 15 / 2 * y ^ 8 - 7 * y ^ 6 + 5 * y ^ 4 - 3 / 2 * y ^ 2 + 5 / 66) / 1814400) (by fun_prop) (by norm_num)
    exact this
  have hd : ∀ x : ℝ, HasDerivWithinAt (fun x : ℝ => ((Int.fract x) ^ 10 - 5 * (Int.fract x) ^ 9 + 15 / 2 * (Int.fract x) ^ 8 - 7 * (Int.fract x) ^ 6 + 5 * (Int.fract x) ^ 4 - 3 / 2 * (Int.fract x) ^ 2 + 5 / 66) / 1814400)
      (((Int.fract x) ^ 9 - 9 / 2 * (Int.fract x) ^ 8 + 6 * (Int.fract x) ^ 7 - 21 / 5 * (Int.fract x) ^ 5 + 2 * (Int.fract x) ^ 3 - 3 / 10 * Int.fract x) / 181440) (Ioi x) x := by
    intro x
    have hf := hasDerivWithinAt_fract x
    have := (((((((hf.pow 10).sub ((hf.pow 9).const_mul 5)).add ((hf.pow 8).const_mul (15 / 2))).sub
      ((hf.pow 6).const_mul 7)).add ((hf.pow 4).const_mul 5)).sub ((hf.pow 2).const_mul (3 / 2))).add_const
      (5 / 66 : ℝ)).div_const 1814400
    convert this using 1
    simp
    ring
  have h := ibp_gen2 hc hd (by fun_prop) (by fun_prop) abs_B10_le abs_B9_le
    (P0 := 1 / 23950080) (by intro n; simp; norm_num) (a := -s - 9) (by simp; linarith)
  have e : (-s - 9 - 1) = -s - 10 := by ring
  rw [e] at h
  push_cast at h ⊢
  linear_combination h

/-- Euler Maclaurin from `n = 2` with five Bernoulli terms, Edwards 1974 Chapter 6. -/
theorem riemannZeta_eq_EM10_two {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta s = 1 + (2 : ℂ) ^ (-s) * (1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680 - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / 154828800 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) / 24524881920) -
      s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) * (s + 9) / 2 *
        ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 10 - 5 * (Int.fract x) ^ 9 + 15 / 2 * (Int.fract x) ^ 8 - 7 * (Int.fract x) ^ 6 + 5 * (Int.fract x) ^ 4 - 3 / 2 * (Int.fract x) ^ 2 + 5 / 66) / 1814400 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 10) := by
  have h8 := ibp8_two hs
  have h9 := ibp9_two hs
  have p9 : (2 : ℂ) ^ (-s - 9) = (2 : ℂ) ^ (-s) / 512 := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero]
    have : (2 : ℂ) ^ (-(9 : ℂ)) = 1 / 512 := by
      rw [Complex.cpow_neg]
      norm_num
    rw [this]
    ring
  rw [p9] at h9
  rw [riemannZeta_eq_EM8_two hs h1, h8, h9]
  ring

set_option maxHeartbeats 4000000 in
/-- Certificate piece on `[1521/16, 3121/32]`, proved monomial by monomial. -/
lemma coeff_ten_lo (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (1521 / 16 : ℝ) ≤ x) (hb : x ≤ (3121 / 32 : ℝ)) :
    0 < (-25 * x ^ 10 - 13045 * x ^ 9 - 2595234 * x ^ 8 - 193379258 * x ^ 7 - 1597861901 * x ^ 6 - 3832121129169 * x ^ 5 - 1571785393529416 * x ^ 4 - 261040919148438928 * x ^ 3 - 24055735633592557824 * x ^ 2 + 8107574657197912621056 * x - 24448245044588203474944) +
      (-1750 * x ^ 9 - 492000 * x ^ 8 + 38525340 * x ^ 7 + 38581681240 * x ^ 6 + 7587412505130 * x ^ 5 + 605199192832920 * x ^ 4 - 15638776884922720 * x ^ 3 - 7542413597586176640 * x ^ 2 + 15216837965795910942720 * x - 23620366137461059878912) * g +
      (-250 * x ^ 9 - 152565 * x ^ 8 - 16093512 * x ^ 7 + 3905038690 * x ^ 6 + 1351046020410 * x ^ 5 + 198581356189035 * x ^ 4 + 13974955792304432 * x ^ 3 - 197836307151050928 * x ^ 2 + 6589418657755888369152 * x - 20659617613465616646144) * g ^ 2 +
      (-15750 * x ^ 8 - 4100400 * x ^ 7 + 321860580 * x ^ 6 + 111404500800 * x ^ 5 + 2662395507090 * x ^ 4 - 54017143147200 * x ^ 3 + 42812547705160800 * x ^ 2 + 48196865983875840 * x + 1910923758458725662720) * g ^ 3 +
      (-1125 * x ^ 8 - 750900 * x ^ 7 - 47533392 * x ^ 6 + 15998011518 * x ^ 5 - 1588917185691 * x ^ 4 - 713103623647146 * x ^ 3 - 37666916181357504 * x ^ 2 + 1223976919532846928 * x + 6668128135911993106176) * g ^ 4 +
      (-63000 * x ^ 7 - 14926800 * x ^ 6 + 974749740 * x ^ 5 + 36563650200 * x ^ 4 - 104885546395740 * x ^ 3 - 10130925429907920 * x ^ 2 + 132132083074671840 * x + 2168835957799044480) * g ^ 5 +
      (-3000 * x ^ 7 - 2080260 * x ^ 6 - 92569704 * x ^ 5 + 20588874570 * x ^ 4 - 6313549914804 * x ^ 3 - 966800898621354 * x ^ 2 + 27220674055009232 * x + 50477929272111728) * g ^ 6 +
      (-147000 * x ^ 6 - 31004400 * x ^ 5 + 1394226900 * x ^ 4 - 170025134400 * x ^ 3 - 45661875184860 * x ^ 2 + 6746648049765120 * x - 23084615618963680) * g ^ 7 +
      (-5250 * x ^ 6 - 3612630 * x ^ 5 - 131454180 * x ^ 4 + 7244430930 * x ^ 3 - 2436334712691 * x ^ 2 + 853908134756715 * x - 2345974015290616) * g ^ 8 +
      (-220500 * x ^ 5 - 40194000 * x ^ 4 + 918234900 * x ^ 3 - 194137515000 * x ^ 2 + 52063943539410 * x - 262363506547080) * g ^ 9 +
      (-6300 * x ^ 5 - 4104870 * x ^ 4 - 132847704 * x ^ 3 - 4456384218 * x ^ 2 + 947494302810 * x - 36563533315281) * g ^ 10 +
      (-220500 * x ^ 4 - 33306000 * x ^ 3 + 117964140 * x ^ 2 - 57477442560 * x - 2234710673430) * g ^ 11 +
      (-5250 * x ^ 4 - 3064740 * x ^ 3 - 87811392 * x ^ 2 - 3496733590 * x + 11840168699) * g ^ 12 +
      (-147000 * x ^ 3 - 17228400 * x ^ 2 - 154131420 * x + 2894107400) * g ^ 13 +
      (-3000 * x ^ 3 - 1454100 * x ^ 2 - 33355512 * x - 485199442) * g ^ 14 +
      (-63000 * x ^ 2 - 5086800 * x - 56673060) * g ^ 15 +
      (-1125 * x ^ 2 - 398685 * x - 5472234) * g ^ 16 +
      (-15750 * x - 656400) * g ^ 17 +
      (-250 * x - 48205) * g ^ 18 +
      (-1750) * g ^ 19 +
      (-25) * g ^ 20 := by
  have hx : 0 ≤ x := by linarith
  have u1 : x ^ 1 ≤ (3121 / 32 : ℝ) := by
    calc x ^ 1 ≤ (3121 / 32 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (1521 / 16 : ℝ) ≤ x ^ 1 := by
    calc (1521 / 16 : ℝ) = (1521 / 16 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (9740641 / 1024 : ℝ) := by
    calc x ^ 2 ≤ (3121 / 32 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (2313441 / 256 : ℝ) ≤ x ^ 2 := by
    calc (2313441 / 256 : ℝ) = (1521 / 16 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (30400540561 / 32768 : ℝ) := by
    calc x ^ 3 ≤ (3121 / 32 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (3518743761 / 4096 : ℝ) ≤ x ^ 3 := by
    calc (3518743761 / 4096 : ℝ) = (1521 / 16 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (94880087090881 / 1048576 : ℝ) := by
    calc x ^ 4 ≤ (3121 / 32 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (5352009260481 / 65536 : ℝ) ≤ x ^ 4 := by
    calc (5352009260481 / 65536 : ℝ) = (1521 / 16 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (296120751810639601 / 33554432 : ℝ) := by
    calc x ^ 5 ≤ (3121 / 32 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (8140406085191601 / 1048576 : ℝ) ≤ x ^ 5 := by
    calc (8140406085191601 / 1048576 : ℝ) = (1521 / 16 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (924192866401006194721 / 1073741824 : ℝ) := by
    calc x ^ 6 ≤ (3121 / 32 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (12381557655576425121 / 16777216 : ℝ) ≤ x ^ 6 := by
    calc (12381557655576425121 / 16777216 : ℝ) = (1521 / 16 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (2884405936037540333724241 / 34359738368 : ℝ) := by
    calc x ^ 7 ≤ (3121 / 32 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (18832349194131742609041 / 268435456 : ℝ) ≤ x ^ 7 := by
    calc (18832349194131742609041 / 268435456 : ℝ) = (1521 / 16 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have u8 : x ^ 8 ≤ (9002230926373163381553356161 / 1099511627776 : ℝ) := by
    calc x ^ 8 ≤ (3121 / 32 : ℝ) ^ 8 := pow_le_pow_left₀ hx hb 8
      _ = _ := by norm_num
  have l8 : (28644003124274380508351361 / 4294967296 : ℝ) ≤ x ^ 8 := by
    calc (28644003124274380508351361 / 4294967296 : ℝ) = (1521 / 16 : ℝ) ^ 8 := by norm_num
      _ ≤ x ^ 8 := pow_le_pow_left₀ (by norm_num) ha 8
  have u9 : x ^ 9 ≤ (28095962721210642913828024578481 / 35184372088832 : ℝ) := by
    calc x ^ 9 ≤ (3121 / 32 : ℝ) ^ 9 := pow_le_pow_left₀ hx hb 9
      _ = _ := by norm_num
  have l9 : (43567528752021332753202420081 / 68719476736 : ℝ) ≤ x ^ 9 := by
    calc (43567528752021332753202420081 / 68719476736 : ℝ) = (1521 / 16 : ℝ) ^ 9 := by norm_num
      _ ≤ x ^ 9 := pow_le_pow_left₀ (by norm_num) ha 9
  have u10 : x ^ 10 ≤ (87687499652898416534057264709439201 / 1125899906842624 : ℝ) := by
    calc x ^ 10 ≤ (3121 / 32 : ℝ) ^ 10 := pow_le_pow_left₀ hx hb 10
      _ = _ := by norm_num
  have l10 : (66266211231824447117620880943201 / 1099511627776 : ℝ) ≤ x ^ 10 := by
    calc (66266211231824447117620880943201 / 1099511627776 : ℝ) = (1521 / 16 : ℝ) ^ 10 := by norm_num
      _ ≤ x ^ 10 := pow_le_pow_left₀ (by norm_num) ha 10
  have hc0 : (48007998461694129342020 : ℝ) ≤ -25 * x ^ 10 - 13045 * x ^ 9 - 2595234 * x ^ 8 - 193379258 * x ^ 7 - 1597861901 * x ^ 6 - 3832121129169 * x ^ 5 - 1571785393529416 * x ^ 4 - 261040919148438928 * x ^ 3 - 24055735633592557824 * x ^ 2 + 8107574657197912621056 * x - 24448245044588203474944 := by linarith
  have hc1 : (1470752719738253465499305 : ℝ) ≤ -1750 * x ^ 9 - 492000 * x ^ 8 + 38525340 * x ^ 7 + 38581681240 * x ^ 6 + 7587412505130 * x ^ 5 + 605199192832920 * x ^ 4 - 15638776884922720 * x ^ 3 - 7542413597586176640 * x ^ 2 + 15216837965795910942720 * x - 23620366137461059878912 := by linarith
  have t1 : 0 ≤ (-1750 * x ^ 9 - 492000 * x ^ 8 + 38525340 * x ^ 7 + 38581681240 * x ^ 6 + 7587412505130 * x ^ 5 + 605199192832920 * x ^ 4 - 15638776884922720 * x ^ 3 - 7542413597586176640 * x ^ 2 + 15216837965795910942720 * x - 23620366137461059878912) * g := mul_nonneg (by linarith) (by positivity)
  have hc2 : (642658449558684920142637 : ℝ) ≤ -250 * x ^ 9 - 152565 * x ^ 8 - 16093512 * x ^ 7 + 3905038690 * x ^ 6 + 1351046020410 * x ^ 5 + 198581356189035 * x ^ 4 + 13974955792304432 * x ^ 3 - 197836307151050928 * x ^ 2 + 6589418657755888369152 * x - 20659617613465616646144 := by linarith
  have t2 : 0 ≤ (-250 * x ^ 9 - 152565 * x ^ 8 - 16093512 * x ^ 7 + 3905038690 * x ^ 6 + 1351046020410 * x ^ 5 + 198581356189035 * x ^ 4 + 13974955792304432 * x ^ 3 - 197836307151050928 * x ^ 2 + 6589418657755888369152 * x - 20659617613465616646144) * g ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hc3 : (3098936372936468037207 : ℝ) ≤ -15750 * x ^ 8 - 4100400 * x ^ 7 + 321860580 * x ^ 6 + 111404500800 * x ^ 5 + 2662395507090 * x ^ 4 - 54017143147200 * x ^ 3 + 42812547705160800 * x ^ 2 + 48196865983875840 * x + 1910923758458725662720 := by linarith
  have t3 : 0 ≤ (-15750 * x ^ 8 - 4100400 * x ^ 7 + 321860580 * x ^ 6 + 111404500800 * x ^ 5 + 2662395507090 * x ^ 4 - 54017143147200 * x ^ 3 + 42812547705160800 * x ^ 2 + 48196865983875840 * x + 1910923758458725662720) * g ^ 3 := mul_nonneg (by linarith) (by positivity)
  have hc4 : (5631863909692911401174 : ℝ) ≤ -1125 * x ^ 8 - 750900 * x ^ 7 - 47533392 * x ^ 6 + 15998011518 * x ^ 5 - 1588917185691 * x ^ 4 - 713103623647146 * x ^ 3 - 37666916181357504 * x ^ 2 + 1223976919532846928 * x + 6668128135911993106176 := by linarith
  have t4 : 0 ≤ (-1125 * x ^ 8 - 750900 * x ^ 7 - 47533392 * x ^ 6 + 15998011518 * x ^ 5 - 1588917185691 * x ^ 4 - 713103623647146 * x ^ 3 - 37666916181357504 * x ^ 2 + 1223976919532846928 * x + 6668128135911993106176) * g ^ 4 := mul_nonneg (by linarith) (by positivity)
  have hc5 : (-186530119855782385893 : ℝ) ≤ -63000 * x ^ 7 - 14926800 * x ^ 6 + 974749740 * x ^ 5 + 36563650200 * x ^ 4 - 104885546395740 * x ^ 3 - 10130925429907920 * x ^ 2 + 132132083074671840 * x + 2168835957799044480 := by linarith
  have t5 : (-186530119855782385893 : ℝ) ≤ (-63000 * x ^ 7 - 14926800 * x ^ 6 + 974749740 * x ^ 5 + 36563650200 * x ^ 4 - 104885546395740 * x ^ 3 - 10130925429907920 * x ^ 2 + 132132083074671840 * x + 2168835957799044480) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-13593709728792964234 : ℝ) ≤ -3000 * x ^ 7 - 2080260 * x ^ 6 - 92569704 * x ^ 5 + 20588874570 * x ^ 4 - 6313549914804 * x ^ 3 - 966800898621354 * x ^ 2 + 27220674055009232 * x + 50477929272111728 := by linarith
  have t6 : (-13593709728792964234 : ℝ) ≤ (-3000 * x ^ 7 - 2080260 * x ^ 6 - 92569704 * x ^ 5 + 20588874570 * x ^ 4 - 6313549914804 * x ^ 3 - 966800898621354 * x ^ 2 + 27220674055009232 * x + 50477929272111728) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-260106645135322678 : ℝ) ≤ -147000 * x ^ 6 - 31004400 * x ^ 5 + 1394226900 * x ^ 4 - 170025134400 * x ^ 3 - 45661875184860 * x ^ 2 + 6746648049765120 * x - 23084615618963680 := by linarith
  have t7 : (-260106645135322678 : ℝ) ≤ (-147000 * x ^ 6 - 31004400 * x ^ 5 + 1394226900 * x ^ 4 - 170025134400 * x ^ 3 - 45661875184860 * x ^ 2 + 6746648049765120 * x - 23084615618963680) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (13581721373149253 : ℝ) ≤ -5250 * x ^ 6 - 3612630 * x ^ 5 - 131454180 * x ^ 4 + 7244430930 * x ^ 3 - 2436334712691 * x ^ 2 + 853908134756715 * x - 2345974015290616 := by linarith
  have t8 : 0 ≤ (-5250 * x ^ 6 - 3612630 * x ^ 5 - 131454180 * x ^ 4 + 7244430930 * x ^ 3 - 2436334712691 * x ^ 2 + 853908134756715 * x - 2345974015290616) * g ^ 8 := mul_nonneg (by linarith) (by positivity)
  have hc9 : (-1953784952997563 : ℝ) ≤ -220500 * x ^ 5 - 40194000 * x ^ 4 + 918234900 * x ^ 3 - 194137515000 * x ^ 2 + 52063943539410 * x - 262363506547080 := by linarith
  have t9 : (-1953784952997563 : ℝ) ≤ (-220500 * x ^ 5 - 40194000 * x ^ 4 + 918234900 * x ^ 3 - 194137515000 * x ^ 2 + 52063943539410 * x - 262363506547080) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-539158574255230 : ℝ) ≤ -6300 * x ^ 5 - 4104870 * x ^ 4 - 132847704 * x ^ 3 - 4456384218 * x ^ 2 + 947494302810 * x - 36563533315281 := by linarith
  have t10 : (-539158574255230 : ℝ) ≤ (-6300 * x ^ 5 - 4104870 * x ^ 4 - 132847704 * x ^ 3 - 4456384218 * x ^ 2 + 947494302810 * x - 36563533315281) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-57626077209008 : ℝ) ≤ -220500 * x ^ 4 - 33306000 * x ^ 3 + 117964140 * x ^ 2 - 57477442560 * x - 2234710673430 := by linarith
  have t11 : (-57626077209008 : ℝ) ≤ (-220500 * x ^ 4 - 33306000 * x ^ 3 + 117964140 * x ^ 2 - 57477442560 * x - 2234710673430) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-4482852753674 : ℝ) ≤ -5250 * x ^ 4 - 3064740 * x ^ 3 - 87811392 * x ^ 2 - 3496733590 * x + 11840168699 := by linarith
  have t12 : (-4482852753674 : ℝ) ≤ (-5250 * x ^ 4 - 3064740 * x ^ 3 - 87811392 * x ^ 2 - 3496733590 * x + 11840168699) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  have hc13 : (-312400380672 : ℝ) ≤ -147000 * x ^ 3 - 17228400 * x ^ 2 - 154131420 * x + 2894107400 := by linarith
  have t13 : (-312400380672 : ℝ) ≤ (-147000 * x ^ 3 - 17228400 * x ^ 2 - 154131420 * x + 2894107400) * g ^ 13 := by
    have g0 : 0 ≤ g ^ 13 := by positivity
    have g1 : g ^ 13 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc13) g0]
  have hc14 : (-20353557304 : ℝ) ≤ -3000 * x ^ 3 - 1454100 * x ^ 2 - 33355512 * x - 485199442 := by linarith
  have t14 : (-20353557304 : ℝ) ≤ (-3000 * x ^ 3 - 1454100 * x ^ 2 - 33355512 * x - 485199442) * g ^ 14 := by
    have g0 : 0 ≤ g ^ 14 := by positivity
    have g1 : g ^ 14 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc14) g0]
  have hc15 : (-1152072741 : ℝ) ≤ -63000 * x ^ 2 - 5086800 * x - 56673060 := by linarith
  have t15 : (-1152072741 : ℝ) ≤ (-63000 * x ^ 2 - 5086800 * x - 56673060) * g ^ 15 := by
    have g0 : 0 ≤ g ^ 15 := by positivity
    have g1 : g ^ 15 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc15) g0]
  have hc16 : (-55057869 : ℝ) ≤ -1125 * x ^ 2 - 398685 * x - 5472234 := by linarith
  have t16 : (-55057869 : ℝ) ≤ (-1125 * x ^ 2 - 398685 * x - 5472234) * g ^ 16 := by
    have g0 : 0 ≤ g ^ 16 := by positivity
    have g1 : g ^ 16 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc16) g0]
  have hc17 : (-2192518 : ℝ) ≤ -15750 * x - 656400 := by linarith
  have t17 : (-2192518 : ℝ) ≤ (-15750 * x - 656400) * g ^ 17 := by
    have g0 : 0 ≤ g ^ 17 := by positivity
    have g1 : g ^ 17 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc17) g0]
  have hc18 : (-72588 : ℝ) ≤ -250 * x - 48205 := by linarith
  have t18 : (-72588 : ℝ) ≤ (-250 * x - 48205) * g ^ 18 := by
    have g0 : 0 ≤ g ^ 18 := by positivity
    have g1 : g ^ 18 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc18) g0]
  have hc19 : (-1750 : ℝ) ≤ -1750 := by norm_num
  have t19 : (-1750 : ℝ) ≤ (-1750) * g ^ 19 := by
    have g0 : 0 ≤ g ^ 19 := by positivity
    have g1 : g ^ 19 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc19) g0]
  have hc20 : (-25 : ℝ) ≤ -25 := by norm_num
  have t20 : (-25 : ℝ) ≤ (-25) * g ^ 20 := by
    have g0 : 0 ≤ g ^ 20 := by positivity
    have g1 : g ^ 20 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc20) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece on `[3121/32, 100]`, proved monomial by monomial. -/
lemma coeff_ten_hi (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (3121 / 32 : ℝ) ≤ x) (hb : x ≤ (100 : ℝ)) :
    0 < (-25 * x ^ 10 - 13045 * x ^ 9 - 2595234 * x ^ 8 - 193379258 * x ^ 7 - 1597861901 * x ^ 6 - 3832121129169 * x ^ 5 - 1571785393529416 * x ^ 4 - 261040919148438928 * x ^ 3 - 24055735633592557824 * x ^ 2 + 8107574657197912621056 * x - 24448245044588203474944) +
      (-1750 * x ^ 9 - 492000 * x ^ 8 + 38525340 * x ^ 7 + 38581681240 * x ^ 6 + 7587412505130 * x ^ 5 + 605199192832920 * x ^ 4 - 15638776884922720 * x ^ 3 - 7542413597586176640 * x ^ 2 + 15216837965795910942720 * x - 23620366137461059878912) * g +
      (-250 * x ^ 9 - 152565 * x ^ 8 - 16093512 * x ^ 7 + 3905038690 * x ^ 6 + 1351046020410 * x ^ 5 + 198581356189035 * x ^ 4 + 13974955792304432 * x ^ 3 - 197836307151050928 * x ^ 2 + 6589418657755888369152 * x - 20659617613465616646144) * g ^ 2 +
      (-15750 * x ^ 8 - 4100400 * x ^ 7 + 321860580 * x ^ 6 + 111404500800 * x ^ 5 + 2662395507090 * x ^ 4 - 54017143147200 * x ^ 3 + 42812547705160800 * x ^ 2 + 48196865983875840 * x + 1910923758458725662720) * g ^ 3 +
      (-1125 * x ^ 8 - 750900 * x ^ 7 - 47533392 * x ^ 6 + 15998011518 * x ^ 5 - 1588917185691 * x ^ 4 - 713103623647146 * x ^ 3 - 37666916181357504 * x ^ 2 + 1223976919532846928 * x + 6668128135911993106176) * g ^ 4 +
      (-63000 * x ^ 7 - 14926800 * x ^ 6 + 974749740 * x ^ 5 + 36563650200 * x ^ 4 - 104885546395740 * x ^ 3 - 10130925429907920 * x ^ 2 + 132132083074671840 * x + 2168835957799044480) * g ^ 5 +
      (-3000 * x ^ 7 - 2080260 * x ^ 6 - 92569704 * x ^ 5 + 20588874570 * x ^ 4 - 6313549914804 * x ^ 3 - 966800898621354 * x ^ 2 + 27220674055009232 * x + 50477929272111728) * g ^ 6 +
      (-147000 * x ^ 6 - 31004400 * x ^ 5 + 1394226900 * x ^ 4 - 170025134400 * x ^ 3 - 45661875184860 * x ^ 2 + 6746648049765120 * x - 23084615618963680) * g ^ 7 +
      (-5250 * x ^ 6 - 3612630 * x ^ 5 - 131454180 * x ^ 4 + 7244430930 * x ^ 3 - 2436334712691 * x ^ 2 + 853908134756715 * x - 2345974015290616) * g ^ 8 +
      (-220500 * x ^ 5 - 40194000 * x ^ 4 + 918234900 * x ^ 3 - 194137515000 * x ^ 2 + 52063943539410 * x - 262363506547080) * g ^ 9 +
      (-6300 * x ^ 5 - 4104870 * x ^ 4 - 132847704 * x ^ 3 - 4456384218 * x ^ 2 + 947494302810 * x - 36563533315281) * g ^ 10 +
      (-220500 * x ^ 4 - 33306000 * x ^ 3 + 117964140 * x ^ 2 - 57477442560 * x - 2234710673430) * g ^ 11 +
      (-5250 * x ^ 4 - 3064740 * x ^ 3 - 87811392 * x ^ 2 - 3496733590 * x + 11840168699) * g ^ 12 +
      (-147000 * x ^ 3 - 17228400 * x ^ 2 - 154131420 * x + 2894107400) * g ^ 13 +
      (-3000 * x ^ 3 - 1454100 * x ^ 2 - 33355512 * x - 485199442) * g ^ 14 +
      (-63000 * x ^ 2 - 5086800 * x - 56673060) * g ^ 15 +
      (-1125 * x ^ 2 - 398685 * x - 5472234) * g ^ 16 +
      (-15750 * x - 656400) * g ^ 17 +
      (-250 * x - 48205) * g ^ 18 +
      (-1750) * g ^ 19 +
      (-25) * g ^ 20 := by
  have hx : 0 ≤ x := by linarith
  have u1 : x ^ 1 ≤ (100 : ℝ) := by
    calc x ^ 1 ≤ (100 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (3121 / 32 : ℝ) ≤ x ^ 1 := by
    calc (3121 / 32 : ℝ) = (3121 / 32 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (10000 : ℝ) := by
    calc x ^ 2 ≤ (100 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (9740641 / 1024 : ℝ) ≤ x ^ 2 := by
    calc (9740641 / 1024 : ℝ) = (3121 / 32 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (1000000 : ℝ) := by
    calc x ^ 3 ≤ (100 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (30400540561 / 32768 : ℝ) ≤ x ^ 3 := by
    calc (30400540561 / 32768 : ℝ) = (3121 / 32 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (100000000 : ℝ) := by
    calc x ^ 4 ≤ (100 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (94880087090881 / 1048576 : ℝ) ≤ x ^ 4 := by
    calc (94880087090881 / 1048576 : ℝ) = (3121 / 32 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (10000000000 : ℝ) := by
    calc x ^ 5 ≤ (100 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (296120751810639601 / 33554432 : ℝ) ≤ x ^ 5 := by
    calc (296120751810639601 / 33554432 : ℝ) = (3121 / 32 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (1000000000000 : ℝ) := by
    calc x ^ 6 ≤ (100 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (924192866401006194721 / 1073741824 : ℝ) ≤ x ^ 6 := by
    calc (924192866401006194721 / 1073741824 : ℝ) = (3121 / 32 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (100000000000000 : ℝ) := by
    calc x ^ 7 ≤ (100 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (2884405936037540333724241 / 34359738368 : ℝ) ≤ x ^ 7 := by
    calc (2884405936037540333724241 / 34359738368 : ℝ) = (3121 / 32 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have u8 : x ^ 8 ≤ (10000000000000000 : ℝ) := by
    calc x ^ 8 ≤ (100 : ℝ) ^ 8 := pow_le_pow_left₀ hx hb 8
      _ = _ := by norm_num
  have l8 : (9002230926373163381553356161 / 1099511627776 : ℝ) ≤ x ^ 8 := by
    calc (9002230926373163381553356161 / 1099511627776 : ℝ) = (3121 / 32 : ℝ) ^ 8 := by norm_num
      _ ≤ x ^ 8 := pow_le_pow_left₀ (by norm_num) ha 8
  have u9 : x ^ 9 ≤ (1000000000000000000 : ℝ) := by
    calc x ^ 9 ≤ (100 : ℝ) ^ 9 := pow_le_pow_left₀ hx hb 9
      _ = _ := by norm_num
  have l9 : (28095962721210642913828024578481 / 35184372088832 : ℝ) ≤ x ^ 9 := by
    calc (28095962721210642913828024578481 / 35184372088832 : ℝ) = (3121 / 32 : ℝ) ^ 9 := by norm_num
      _ ≤ x ^ 9 := pow_le_pow_left₀ (by norm_num) ha 9
  have u10 : x ^ 10 ≤ (100000000000000000000 : ℝ) := by
    calc x ^ 10 ≤ (100 : ℝ) ^ 10 := pow_le_pow_left₀ hx hb 10
      _ = _ := by norm_num
  have l10 : (87687499652898416534057264709439201 / 1125899906842624 : ℝ) ≤ x ^ 10 := by
    calc (87687499652898416534057264709439201 / 1125899906842624 : ℝ) = (3121 / 32 : ℝ) ^ 10 := by norm_num
      _ ≤ x ^ 10 := pow_le_pow_left₀ (by norm_num) ha 10
  have hc0 : (6762491910249605607424 : ℝ) ≤ -25 * x ^ 10 - 13045 * x ^ 9 - 2595234 * x ^ 8 - 193379258 * x ^ 7 - 1597861901 * x ^ 6 - 3832121129169 * x ^ 5 - 1571785393529416 * x ^ 4 - 261040919148438928 * x ^ 3 - 24055735633592557824 * x ^ 2 + 8107574657197912621056 * x - 24448245044588203474944 := by linarith
  have hc1 : (1520926972575569200385011 : ℝ) ≤ -1750 * x ^ 9 - 492000 * x ^ 8 + 38525340 * x ^ 7 + 38581681240 * x ^ 6 + 7587412505130 * x ^ 5 + 605199192832920 * x ^ 4 - 15638776884922720 * x ^ 3 - 7542413597586176640 * x ^ 2 + 15216837965795910942720 * x - 23620366137461059878912 := by linarith
  have t1 : 0 ≤ (-1750 * x ^ 9 - 492000 * x ^ 8 + 38525340 * x ^ 7 + 38581681240 * x ^ 6 + 7587412505130 * x ^ 5 + 605199192832920 * x ^ 4 - 15638776884922720 * x ^ 3 - 7542413597586176640 * x ^ 2 + 15216837965795910942720 * x - 23620366137461059878912) * g := mul_nonneg (by linarith) (by positivity)
  have hc2 : (662869357804064204723134 : ℝ) ≤ -250 * x ^ 9 - 152565 * x ^ 8 - 16093512 * x ^ 7 + 3905038690 * x ^ 6 + 1351046020410 * x ^ 5 + 198581356189035 * x ^ 4 + 13974955792304432 * x ^ 3 - 197836307151050928 * x ^ 2 + 6589418657755888369152 * x - 20659617613465616646144 := by linarith
  have t2 : 0 ≤ (-250 * x ^ 9 - 152565 * x ^ 8 - 16093512 * x ^ 7 + 3905038690 * x ^ 6 + 1351046020410 * x ^ 5 + 198581356189035 * x ^ 4 + 13974955792304432 * x ^ 3 - 197836307151050928 * x ^ 2 + 6589418657755888369152 * x - 20659617613465616646144) * g ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hc3 : (3202407784681733703072 : ℝ) ≤ -15750 * x ^ 8 - 4100400 * x ^ 7 + 321860580 * x ^ 6 + 111404500800 * x ^ 5 + 2662395507090 * x ^ 4 - 54017143147200 * x ^ 3 + 42812547705160800 * x ^ 2 + 48196865983875840 * x + 1910923758458725662720 := by linarith
  have t3 : 0 ≤ (-15750 * x ^ 8 - 4100400 * x ^ 7 + 321860580 * x ^ 6 + 111404500800 * x ^ 5 + 2662395507090 * x ^ 4 - 54017143147200 * x ^ 3 + 42812547705160800 * x ^ 2 + 48196865983875840 * x + 1910923758458725662720) * g ^ 3 := mul_nonneg (by linarith) (by positivity)
  have hc4 : (5546150068068837845749 : ℝ) ≤ -1125 * x ^ 8 - 750900 * x ^ 7 - 47533392 * x ^ 6 + 15998011518 * x ^ 5 - 1588917185691 * x ^ 4 - 713103623647146 * x ^ 3 - 37666916181357504 * x ^ 2 + 1223976919532846928 * x + 6668128135911993106176 := by linarith
  have t4 : 0 ≤ (-1125 * x ^ 8 - 750900 * x ^ 7 - 47533392 * x ^ 6 + 15998011518 * x ^ 5 - 1588917185691 * x ^ 4 - 713103623647146 * x ^ 3 - 37666916181357504 * x ^ 2 + 1223976919532846928 * x + 6668128135911993106176) * g ^ 4 := mul_nonneg (by linarith) (by positivity)
  have hc5 : (-200455056117744168103 : ℝ) ≤ -63000 * x ^ 7 - 14926800 * x ^ 6 + 974749740 * x ^ 5 + 36563650200 * x ^ 4 - 104885546395740 * x ^ 3 - 10130925429907920 * x ^ 2 + 132132083074671840 * x + 2168835957799044480 := by linarith
  have t5 : (-200455056117744168103 : ℝ) ≤ (-63000 * x ^ 7 - 14926800 * x ^ 6 + 974749740 * x ^ 5 + 36563650200 * x ^ 4 - 104885546395740 * x ^ 3 - 10130925429907920 * x ^ 2 + 132132083074671840 * x + 2168835957799044480) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-14719193461280767355 : ℝ) ≤ -3000 * x ^ 7 - 2080260 * x ^ 6 - 92569704 * x ^ 5 + 20588874570 * x ^ 4 - 6313549914804 * x ^ 3 - 966800898621354 * x ^ 2 + 27220674055009232 * x + 50477929272111728 := by linarith
  have t6 : (-14719193461280767355 : ℝ) ≤ (-3000 * x ^ 7 - 2080260 * x ^ 6 - 92569704 * x ^ 5 + 20588874570 * x ^ 4 - 6313549914804 * x ^ 3 - 966800898621354 * x ^ 2 + 27220674055009232 * x + 50477929272111728) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-322607278422416634 : ℝ) ≤ -147000 * x ^ 6 - 31004400 * x ^ 5 + 1394226900 * x ^ 4 - 170025134400 * x ^ 3 - 45661875184860 * x ^ 2 + 6746648049765120 * x - 23084615618963680 := by linarith
  have t7 : (-322607278422416634 : ℝ) ≤ (-147000 * x ^ 6 - 31004400 * x ^ 5 + 1394226900 * x ^ 4 - 170025134400 * x ^ 3 - 45661875184860 * x ^ 2 + 6746648049765120 * x - 23084615618963680) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (8772715735434651 : ℝ) ≤ -5250 * x ^ 6 - 3612630 * x ^ 5 - 131454180 * x ^ 4 + 7244430930 * x ^ 3 - 2436334712691 * x ^ 2 + 853908134756715 * x - 2345974015290616 := by linarith
  have t8 : 0 ≤ (-5250 * x ^ 6 - 3612630 * x ^ 5 - 131454180 * x ^ 4 + 7244430930 * x ^ 3 - 2436334712691 * x ^ 2 + 853908134756715 * x - 2345974015290616) * g ^ 8 := mul_nonneg (by linarith) (by positivity)
  have hc9 : (-2498383934398937 : ℝ) ≤ -220500 * x ^ 5 - 40194000 * x ^ 4 + 918234900 * x ^ 3 - 194137515000 * x ^ 2 + 52063943539410 * x - 262363506547080 := by linarith
  have t9 : (-2498383934398937 : ℝ) ≤ (-220500 * x ^ 5 - 40194000 * x ^ 4 + 918234900 * x ^ 3 - 194137515000 * x ^ 2 + 52063943539410 * x - 262363506547080) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-595051775774344 : ℝ) ≤ -6300 * x ^ 5 - 4104870 * x ^ 4 - 132847704 * x ^ 3 - 4456384218 * x ^ 2 + 947494302810 * x - 36563533315281 := by linarith
  have t10 : (-595051775774344 : ℝ) ≤ (-6300 * x ^ 5 - 4104870 * x ^ 4 - 132847704 * x ^ 3 - 4456384218 * x ^ 2 + 947494302810 * x - 36563533315281) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-62216339364378 : ℝ) ≤ -220500 * x ^ 4 - 33306000 * x ^ 3 + 117964140 * x ^ 2 - 57477442560 * x - 2234710673430 := by linarith
  have t11 : (-62216339364378 : ℝ) ≤ (-220500 * x ^ 4 - 33306000 * x ^ 3 + 117964140 * x ^ 2 - 57477442560 * x - 2234710673430) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-4805687110301 : ℝ) ≤ -5250 * x ^ 4 - 3064740 * x ^ 3 - 87811392 * x ^ 2 - 3496733590 * x + 11840168699 := by linarith
  have t12 : (-4805687110301 : ℝ) ≤ (-5250 * x ^ 4 - 3064740 * x ^ 3 - 87811392 * x ^ 2 - 3496733590 * x + 11840168699) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  have hc13 : (-331803034600 : ℝ) ≤ -147000 * x ^ 3 - 17228400 * x ^ 2 - 154131420 * x + 2894107400 := by linarith
  have t13 : (-331803034600 : ℝ) ≤ (-147000 * x ^ 3 - 17228400 * x ^ 2 - 154131420 * x + 2894107400) * g ^ 13 := by
    have g0 : 0 ≤ g ^ 13 := by positivity
    have g1 : g ^ 13 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc13) g0]
  have hc14 : (-21361750642 : ℝ) ≤ -3000 * x ^ 3 - 1454100 * x ^ 2 - 33355512 * x - 485199442 := by linarith
  have t14 : (-21361750642 : ℝ) ≤ (-3000 * x ^ 3 - 1454100 * x ^ 2 - 33355512 * x - 485199442) * g ^ 14 := by
    have g0 : 0 ≤ g ^ 14 := by positivity
    have g1 : g ^ 14 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc14) g0]
  have hc15 : (-1195353060 : ℝ) ≤ -63000 * x ^ 2 - 5086800 * x - 56673060 := by linarith
  have t15 : (-1195353060 : ℝ) ≤ (-63000 * x ^ 2 - 5086800 * x - 56673060) * g ^ 15 := by
    have g0 : 0 ≤ g ^ 15 := by positivity
    have g1 : g ^ 15 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc15) g0]
  have hc16 : (-56590734 : ℝ) ≤ -1125 * x ^ 2 - 398685 * x - 5472234 := by linarith
  have t16 : (-56590734 : ℝ) ≤ (-1125 * x ^ 2 - 398685 * x - 5472234) * g ^ 16 := by
    have g0 : 0 ≤ g ^ 16 := by positivity
    have g1 : g ^ 16 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc16) g0]
  have hc17 : (-2231400 : ℝ) ≤ -15750 * x - 656400 := by linarith
  have t17 : (-2231400 : ℝ) ≤ (-15750 * x - 656400) * g ^ 17 := by
    have g0 : 0 ≤ g ^ 17 := by positivity
    have g1 : g ^ 17 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc17) g0]
  have hc18 : (-73205 : ℝ) ≤ -250 * x - 48205 := by linarith
  have t18 : (-73205 : ℝ) ≤ (-250 * x - 48205) * g ^ 18 := by
    have g0 : 0 ≤ g ^ 18 := by positivity
    have g1 : g ^ 18 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc18) g0]
  have hc19 : (-1750 : ℝ) ≤ -1750 := by norm_num
  have t19 : (-1750 : ℝ) ≤ (-1750) * g ^ 19 := by
    have g0 : 0 ≤ g ^ 19 := by positivity
    have g1 : g ^ 19 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc19) g0]
  have hc20 : (-25 : ℝ) ≤ -25 := by norm_num
  have t20 : (-25 : ℝ) ≤ (-25) * g ^ 20 := by
    have g0 : 0 ≤ g ^ 20 := by positivity
    have g1 : g ^ 20 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc20) g0]
  linarith

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The box polynomial for `H₅ = N₅ / (122624409600 (s - 1))`, proved. -/
lemma box_ten_two_poly (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht0 : 39 / 4 ≤ t) (ht1 : t ≤ 10) :
    ((5 * σ ^ 10 + 175 * σ ^ 9 - 225 * σ ^ 8 * t ^ 2 + 1758 * σ ^ 8 - 6300 * σ ^ 7 * t ^ 2 + 4110 * σ ^ 7 + 1050 * σ ^ 6 * t ^ 4 - 49224 * σ ^ 6 * t ^ 2 + 94317 * σ ^ 6 + 22050 * σ ^ 5 * t ^ 4 - 86310 * σ ^ 5 * t ^ 2 + 921135 * σ ^ 5 - 1050 * σ ^ 4 * t ^ 6 + 123060 * σ ^ 4 * t ^ 4 - 1414755 * σ ^ 4 * t ^ 2 - 18570848 * σ ^ 4 - 14700 * σ ^ 3 * t ^ 6 + 143850 * σ ^ 3 * t ^ 4 - 9211350 * σ ^ 3 * t ^ 2 - 40830700 * σ ^ 3 + 225 * σ ^ 2 * t ^ 8 - 49224 * σ ^ 2 * t ^ 6 + 1414755 * σ ^ 2 * t ^ 4 + 111425088 * σ ^ 2 * t ^ 2 + 5127825168 * σ ^ 2 + 1575 * σ * t ^ 8 - 28770 * σ * t ^ 6 + 4605675 * σ * t ^ 4 + 122492100 * σ * t ^ 2 + 56242759680 * σ - 5 * t ^ 10 + 1758 * t ^ 8 - 94317 * t ^ 6 - 18570848 * t ^ 4 - 5127825168 * t ^ 2 + 183936614400) ^ 2 + (t * (50 * σ ^ 9 + 1575 * σ ^ 8 - 600 * σ ^ 7 * t ^ 2 + 14064 * σ ^ 7 - 14700 * σ ^ 6 * t ^ 2 + 28770 * σ ^ 6 + 1260 * σ ^ 5 * t ^ 4 - 98448 * σ ^ 5 * t ^ 2 + 565902 * σ ^ 5 + 22050 * σ ^ 4 * t ^ 4 - 143850 * σ ^ 4 * t ^ 2 + 4605675 * σ ^ 4 - 600 * σ ^ 3 * t ^ 6 + 98448 * σ ^ 3 * t ^ 4 - 1886340 * σ ^ 3 * t ^ 2 - 74283392 * σ ^ 3 - 6300 * σ ^ 2 * t ^ 6 + 86310 * σ ^ 2 * t ^ 4 - 9211350 * σ ^ 2 * t ^ 2 - 122492100 * σ ^ 2 + 50 * σ * t ^ 8 - 14064 * σ * t ^ 6 + 565902 * σ * t ^ 4 + 74283392 * σ * t ^ 2 + 10255650336 * σ + 175 * t ^ 8 - 4110 * t ^ 6 + 921135 * t ^ 4 + 40830700 * t ^ 2 + 56242759680)) ^ 2) <
      (79 / 100 + 2 * σ / 3) ^ 2 * 122624409600 ^ 2 * ((σ - 1) ^ 2 + t ^ 2) := by
  have hx0 : 1521 / 16 ≤ t ^ 2 := by nlinarith
  have hx1 : t ^ 2 ≤ 100 := by nlinarith
  have h : 0 < (-25 * (t ^ 2) ^ 10 - 13045 * (t ^ 2) ^ 9 - 2595234 * (t ^ 2) ^ 8 - 193379258 * (t ^ 2) ^ 7 - 1597861901 * (t ^ 2) ^ 6 - 3832121129169 * (t ^ 2) ^ 5 - 1571785393529416 * (t ^ 2) ^ 4 - 261040919148438928 * (t ^ 2) ^ 3 - 24055735633592557824 * (t ^ 2) ^ 2 + 8107574657197912621056 * t ^ 2 - 24448245044588203474944) +
      (-1750 * (t ^ 2) ^ 9 - 492000 * (t ^ 2) ^ 8 + 38525340 * (t ^ 2) ^ 7 + 38581681240 * (t ^ 2) ^ 6 + 7587412505130 * (t ^ 2) ^ 5 + 605199192832920 * (t ^ 2) ^ 4 - 15638776884922720 * (t ^ 2) ^ 3 - 7542413597586176640 * (t ^ 2) ^ 2 + 15216837965795910942720 * t ^ 2 - 23620366137461059878912) * σ +
      (-250 * (t ^ 2) ^ 9 - 152565 * (t ^ 2) ^ 8 - 16093512 * (t ^ 2) ^ 7 + 3905038690 * (t ^ 2) ^ 6 + 1351046020410 * (t ^ 2) ^ 5 + 198581356189035 * (t ^ 2) ^ 4 + 13974955792304432 * (t ^ 2) ^ 3 - 197836307151050928 * (t ^ 2) ^ 2 + 6589418657755888369152 * t ^ 2 - 20659617613465616646144) * σ ^ 2 +
      (-15750 * (t ^ 2) ^ 8 - 4100400 * (t ^ 2) ^ 7 + 321860580 * (t ^ 2) ^ 6 + 111404500800 * (t ^ 2) ^ 5 + 2662395507090 * (t ^ 2) ^ 4 - 54017143147200 * (t ^ 2) ^ 3 + 42812547705160800 * (t ^ 2) ^ 2 + 48196865983875840 * t ^ 2 + 1910923758458725662720) * σ ^ 3 +
      (-1125 * (t ^ 2) ^ 8 - 750900 * (t ^ 2) ^ 7 - 47533392 * (t ^ 2) ^ 6 + 15998011518 * (t ^ 2) ^ 5 - 1588917185691 * (t ^ 2) ^ 4 - 713103623647146 * (t ^ 2) ^ 3 - 37666916181357504 * (t ^ 2) ^ 2 + 1223976919532846928 * t ^ 2 + 6668128135911993106176) * σ ^ 4 +
      (-63000 * (t ^ 2) ^ 7 - 14926800 * (t ^ 2) ^ 6 + 974749740 * (t ^ 2) ^ 5 + 36563650200 * (t ^ 2) ^ 4 - 104885546395740 * (t ^ 2) ^ 3 - 10130925429907920 * (t ^ 2) ^ 2 + 132132083074671840 * t ^ 2 + 2168835957799044480) * σ ^ 5 +
      (-3000 * (t ^ 2) ^ 7 - 2080260 * (t ^ 2) ^ 6 - 92569704 * (t ^ 2) ^ 5 + 20588874570 * (t ^ 2) ^ 4 - 6313549914804 * (t ^ 2) ^ 3 - 966800898621354 * (t ^ 2) ^ 2 + 27220674055009232 * t ^ 2 + 50477929272111728) * σ ^ 6 +
      (-147000 * (t ^ 2) ^ 6 - 31004400 * (t ^ 2) ^ 5 + 1394226900 * (t ^ 2) ^ 4 - 170025134400 * (t ^ 2) ^ 3 - 45661875184860 * (t ^ 2) ^ 2 + 6746648049765120 * t ^ 2 - 23084615618963680) * σ ^ 7 +
      (-5250 * (t ^ 2) ^ 6 - 3612630 * (t ^ 2) ^ 5 - 131454180 * (t ^ 2) ^ 4 + 7244430930 * (t ^ 2) ^ 3 - 2436334712691 * (t ^ 2) ^ 2 + 853908134756715 * t ^ 2 - 2345974015290616) * σ ^ 8 +
      (-220500 * (t ^ 2) ^ 5 - 40194000 * (t ^ 2) ^ 4 + 918234900 * (t ^ 2) ^ 3 - 194137515000 * (t ^ 2) ^ 2 + 52063943539410 * t ^ 2 - 262363506547080) * σ ^ 9 +
      (-6300 * (t ^ 2) ^ 5 - 4104870 * (t ^ 2) ^ 4 - 132847704 * (t ^ 2) ^ 3 - 4456384218 * (t ^ 2) ^ 2 + 947494302810 * t ^ 2 - 36563533315281) * σ ^ 10 +
      (-220500 * (t ^ 2) ^ 4 - 33306000 * (t ^ 2) ^ 3 + 117964140 * (t ^ 2) ^ 2 - 57477442560 * t ^ 2 - 2234710673430) * σ ^ 11 +
      (-5250 * (t ^ 2) ^ 4 - 3064740 * (t ^ 2) ^ 3 - 87811392 * (t ^ 2) ^ 2 - 3496733590 * t ^ 2 + 11840168699) * σ ^ 12 +
      (-147000 * (t ^ 2) ^ 3 - 17228400 * (t ^ 2) ^ 2 - 154131420 * t ^ 2 + 2894107400) * σ ^ 13 +
      (-3000 * (t ^ 2) ^ 3 - 1454100 * (t ^ 2) ^ 2 - 33355512 * t ^ 2 - 485199442) * σ ^ 14 +
      (-63000 * (t ^ 2) ^ 2 - 5086800 * t ^ 2 - 56673060) * σ ^ 15 +
      (-1125 * (t ^ 2) ^ 2 - 398685 * t ^ 2 - 5472234) * σ ^ 16 +
      (-15750 * t ^ 2 - 656400) * σ ^ 17 +
      (-250 * t ^ 2 - 48205) * σ ^ 18 +
      (-1750) * σ ^ 19 +
      (-25) * σ ^ 20 := by
    rcases le_total (t ^ 2) (3121 / 32) with hl | hl
    · exact coeff_ten_lo σ (t ^ 2) h0 h1 hx0 hl
    · exact coeff_ten_hi σ (t ^ 2) h0 h1 hl hx1
  have e : (79 / 100 + 2 * σ / 3) ^ 2 * 122624409600 ^ 2 * ((σ - 1) ^ 2 + t ^ 2) -
      ((5 * σ ^ 10 + 175 * σ ^ 9 - 225 * σ ^ 8 * t ^ 2 + 1758 * σ ^ 8 - 6300 * σ ^ 7 * t ^ 2 + 4110 * σ ^ 7 + 1050 * σ ^ 6 * t ^ 4 - 49224 * σ ^ 6 * t ^ 2 + 94317 * σ ^ 6 + 22050 * σ ^ 5 * t ^ 4 - 86310 * σ ^ 5 * t ^ 2 + 921135 * σ ^ 5 - 1050 * σ ^ 4 * t ^ 6 + 123060 * σ ^ 4 * t ^ 4 - 1414755 * σ ^ 4 * t ^ 2 - 18570848 * σ ^ 4 - 14700 * σ ^ 3 * t ^ 6 + 143850 * σ ^ 3 * t ^ 4 - 9211350 * σ ^ 3 * t ^ 2 - 40830700 * σ ^ 3 + 225 * σ ^ 2 * t ^ 8 - 49224 * σ ^ 2 * t ^ 6 + 1414755 * σ ^ 2 * t ^ 4 + 111425088 * σ ^ 2 * t ^ 2 + 5127825168 * σ ^ 2 + 1575 * σ * t ^ 8 - 28770 * σ * t ^ 6 + 4605675 * σ * t ^ 4 + 122492100 * σ * t ^ 2 + 56242759680 * σ - 5 * t ^ 10 + 1758 * t ^ 8 - 94317 * t ^ 6 - 18570848 * t ^ 4 - 5127825168 * t ^ 2 + 183936614400) ^ 2 + (t * (50 * σ ^ 9 + 1575 * σ ^ 8 - 600 * σ ^ 7 * t ^ 2 + 14064 * σ ^ 7 - 14700 * σ ^ 6 * t ^ 2 + 28770 * σ ^ 6 + 1260 * σ ^ 5 * t ^ 4 - 98448 * σ ^ 5 * t ^ 2 + 565902 * σ ^ 5 + 22050 * σ ^ 4 * t ^ 4 - 143850 * σ ^ 4 * t ^ 2 + 4605675 * σ ^ 4 - 600 * σ ^ 3 * t ^ 6 + 98448 * σ ^ 3 * t ^ 4 - 1886340 * σ ^ 3 * t ^ 2 - 74283392 * σ ^ 3 - 6300 * σ ^ 2 * t ^ 6 + 86310 * σ ^ 2 * t ^ 4 - 9211350 * σ ^ 2 * t ^ 2 - 122492100 * σ ^ 2 + 50 * σ * t ^ 8 - 14064 * σ * t ^ 6 + 565902 * σ * t ^ 4 + 74283392 * σ * t ^ 2 + 10255650336 * σ + 175 * t ^ 8 - 4110 * t ^ 6 + 921135 * t ^ 4 + 40830700 * t ^ 2 + 56242759680)) ^ 2) =
      (-25 * (t ^ 2) ^ 10 - 13045 * (t ^ 2) ^ 9 - 2595234 * (t ^ 2) ^ 8 - 193379258 * (t ^ 2) ^ 7 - 1597861901 * (t ^ 2) ^ 6 - 3832121129169 * (t ^ 2) ^ 5 - 1571785393529416 * (t ^ 2) ^ 4 - 261040919148438928 * (t ^ 2) ^ 3 - 24055735633592557824 * (t ^ 2) ^ 2 + 8107574657197912621056 * t ^ 2 - 24448245044588203474944) +
      (-1750 * (t ^ 2) ^ 9 - 492000 * (t ^ 2) ^ 8 + 38525340 * (t ^ 2) ^ 7 + 38581681240 * (t ^ 2) ^ 6 + 7587412505130 * (t ^ 2) ^ 5 + 605199192832920 * (t ^ 2) ^ 4 - 15638776884922720 * (t ^ 2) ^ 3 - 7542413597586176640 * (t ^ 2) ^ 2 + 15216837965795910942720 * t ^ 2 - 23620366137461059878912) * σ +
      (-250 * (t ^ 2) ^ 9 - 152565 * (t ^ 2) ^ 8 - 16093512 * (t ^ 2) ^ 7 + 3905038690 * (t ^ 2) ^ 6 + 1351046020410 * (t ^ 2) ^ 5 + 198581356189035 * (t ^ 2) ^ 4 + 13974955792304432 * (t ^ 2) ^ 3 - 197836307151050928 * (t ^ 2) ^ 2 + 6589418657755888369152 * t ^ 2 - 20659617613465616646144) * σ ^ 2 +
      (-15750 * (t ^ 2) ^ 8 - 4100400 * (t ^ 2) ^ 7 + 321860580 * (t ^ 2) ^ 6 + 111404500800 * (t ^ 2) ^ 5 + 2662395507090 * (t ^ 2) ^ 4 - 54017143147200 * (t ^ 2) ^ 3 + 42812547705160800 * (t ^ 2) ^ 2 + 48196865983875840 * t ^ 2 + 1910923758458725662720) * σ ^ 3 +
      (-1125 * (t ^ 2) ^ 8 - 750900 * (t ^ 2) ^ 7 - 47533392 * (t ^ 2) ^ 6 + 15998011518 * (t ^ 2) ^ 5 - 1588917185691 * (t ^ 2) ^ 4 - 713103623647146 * (t ^ 2) ^ 3 - 37666916181357504 * (t ^ 2) ^ 2 + 1223976919532846928 * t ^ 2 + 6668128135911993106176) * σ ^ 4 +
      (-63000 * (t ^ 2) ^ 7 - 14926800 * (t ^ 2) ^ 6 + 974749740 * (t ^ 2) ^ 5 + 36563650200 * (t ^ 2) ^ 4 - 104885546395740 * (t ^ 2) ^ 3 - 10130925429907920 * (t ^ 2) ^ 2 + 132132083074671840 * t ^ 2 + 2168835957799044480) * σ ^ 5 +
      (-3000 * (t ^ 2) ^ 7 - 2080260 * (t ^ 2) ^ 6 - 92569704 * (t ^ 2) ^ 5 + 20588874570 * (t ^ 2) ^ 4 - 6313549914804 * (t ^ 2) ^ 3 - 966800898621354 * (t ^ 2) ^ 2 + 27220674055009232 * t ^ 2 + 50477929272111728) * σ ^ 6 +
      (-147000 * (t ^ 2) ^ 6 - 31004400 * (t ^ 2) ^ 5 + 1394226900 * (t ^ 2) ^ 4 - 170025134400 * (t ^ 2) ^ 3 - 45661875184860 * (t ^ 2) ^ 2 + 6746648049765120 * t ^ 2 - 23084615618963680) * σ ^ 7 +
      (-5250 * (t ^ 2) ^ 6 - 3612630 * (t ^ 2) ^ 5 - 131454180 * (t ^ 2) ^ 4 + 7244430930 * (t ^ 2) ^ 3 - 2436334712691 * (t ^ 2) ^ 2 + 853908134756715 * t ^ 2 - 2345974015290616) * σ ^ 8 +
      (-220500 * (t ^ 2) ^ 5 - 40194000 * (t ^ 2) ^ 4 + 918234900 * (t ^ 2) ^ 3 - 194137515000 * (t ^ 2) ^ 2 + 52063943539410 * t ^ 2 - 262363506547080) * σ ^ 9 +
      (-6300 * (t ^ 2) ^ 5 - 4104870 * (t ^ 2) ^ 4 - 132847704 * (t ^ 2) ^ 3 - 4456384218 * (t ^ 2) ^ 2 + 947494302810 * t ^ 2 - 36563533315281) * σ ^ 10 +
      (-220500 * (t ^ 2) ^ 4 - 33306000 * (t ^ 2) ^ 3 + 117964140 * (t ^ 2) ^ 2 - 57477442560 * t ^ 2 - 2234710673430) * σ ^ 11 +
      (-5250 * (t ^ 2) ^ 4 - 3064740 * (t ^ 2) ^ 3 - 87811392 * (t ^ 2) ^ 2 - 3496733590 * t ^ 2 + 11840168699) * σ ^ 12 +
      (-147000 * (t ^ 2) ^ 3 - 17228400 * (t ^ 2) ^ 2 - 154131420 * t ^ 2 + 2894107400) * σ ^ 13 +
      (-3000 * (t ^ 2) ^ 3 - 1454100 * (t ^ 2) ^ 2 - 33355512 * t ^ 2 - 485199442) * σ ^ 14 +
      (-63000 * (t ^ 2) ^ 2 - 5086800 * t ^ 2 - 56673060) * σ ^ 15 +
      (-1125 * (t ^ 2) ^ 2 - 398685 * t ^ 2 - 5472234) * σ ^ 16 +
      (-15750 * t ^ 2 - 656400) * σ ^ 17 +
      (-250 * t ^ 2 - 48205) * σ ^ 18 +
      (-1750) * σ ^ 19 +
      (-25) * σ ^ 20 := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- The main term is small: `‖H₅(s)‖ < 79/100 + 2σ/3` on `(0,1) × (39/4, 10]`. Proved. -/
lemma main_ten_two_lt (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 39 / 4 < s.im)
    (ht1 : s.im ≤ 10) :
    ‖1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680 - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / 154828800 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) / 24524881920‖ < 79 / 100 + 2 * s.re / 3 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hM : 1 / 2 + 2 / (s - 1) + s / 24 - s * (s + 1) * (s + 2) / 5760 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) / 967680 - s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) / 154828800 + s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) / 24524881920 = (792 * (160 * (483840 * (s - 1) + 1935360 + 40320 * s * (s - 1) - 168 * (s - 1) * s * (s + 1) * (s + 2) + (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) - (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) + 5 * (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8)) / (122624409600 * (s - 1)) := by
    field_simp
    ring
  rw [hM, norm_div, norm_mul, Complex.norm_ofNat]
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  rw [div_lt_iff₀ (by positivity)]
  set P : ℂ := 792 * (160 * (483840 * (s - 1) + 1935360 + 40320 * s * (s - 1) - 168 * (s - 1) * s * (s + 1) * (s + 2) + (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4)) - (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6)) + 5 * (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6) * (s + 7) * (s + 8) with hP
  have hPre : P.re = 5 * s.re ^ 10 + 175 * s.re ^ 9 - 225 * s.re ^ 8 * s.im ^ 2 + 1758 * s.re ^ 8 - 6300 * s.re ^ 7 * s.im ^ 2 + 4110 * s.re ^ 7 + 1050 * s.re ^ 6 * s.im ^ 4 - 49224 * s.re ^ 6 * s.im ^ 2 + 94317 * s.re ^ 6 + 22050 * s.re ^ 5 * s.im ^ 4 - 86310 * s.re ^ 5 * s.im ^ 2 + 921135 * s.re ^ 5 - 1050 * s.re ^ 4 * s.im ^ 6 + 123060 * s.re ^ 4 * s.im ^ 4 - 1414755 * s.re ^ 4 * s.im ^ 2 - 18570848 * s.re ^ 4 - 14700 * s.re ^ 3 * s.im ^ 6 + 143850 * s.re ^ 3 * s.im ^ 4 - 9211350 * s.re ^ 3 * s.im ^ 2 - 40830700 * s.re ^ 3 + 225 * s.re ^ 2 * s.im ^ 8 - 49224 * s.re ^ 2 * s.im ^ 6 + 1414755 * s.re ^ 2 * s.im ^ 4 + 111425088 * s.re ^ 2 * s.im ^ 2 + 5127825168 * s.re ^ 2 + 1575 * s.re * s.im ^ 8 - 28770 * s.re * s.im ^ 6 + 4605675 * s.re * s.im ^ 4 + 122492100 * s.re * s.im ^ 2 + 56242759680 * s.re - 5 * s.im ^ 10 + 1758 * s.im ^ 8 - 94317 * s.im ^ 6 - 18570848 * s.im ^ 4 - 5127825168 * s.im ^ 2 + 183936614400 := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hPim : P.im = s.im * (50 * s.re ^ 9 + 1575 * s.re ^ 8 - 600 * s.re ^ 7 * s.im ^ 2 + 14064 * s.re ^ 7 - 14700 * s.re ^ 6 * s.im ^ 2 + 28770 * s.re ^ 6 + 1260 * s.re ^ 5 * s.im ^ 4 - 98448 * s.re ^ 5 * s.im ^ 2 + 565902 * s.re ^ 5 + 22050 * s.re ^ 4 * s.im ^ 4 - 143850 * s.re ^ 4 * s.im ^ 2 + 4605675 * s.re ^ 4 - 600 * s.re ^ 3 * s.im ^ 6 + 98448 * s.re ^ 3 * s.im ^ 4 - 1886340 * s.re ^ 3 * s.im ^ 2 - 74283392 * s.re ^ 3 - 6300 * s.re ^ 2 * s.im ^ 6 + 86310 * s.re ^ 2 * s.im ^ 4 - 9211350 * s.re ^ 2 * s.im ^ 2 - 122492100 * s.re ^ 2 + 50 * s.re * s.im ^ 8 - 14064 * s.re * s.im ^ 6 + 565902 * s.re * s.im ^ 4 + 74283392 * s.re * s.im ^ 2 + 10255650336 * s.re + 175 * s.im ^ 8 - 4110 * s.im ^ 6 + 921135 * s.im ^ 4 + 40830700 * s.im ^ 2 + 56242759680) := by
    rw [hP]; simp [Complex.mul_re, Complex.mul_im]; ring
  have hc : 0 < (79 / 100 + 2 * s.re / 3) * (122624409600 * ‖s - 1‖) := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 hc.le
  have e1 : ((79 / 100 + 2 * s.re / 3) * (122624409600 * ‖s - 1‖)) ^ 2 =
      (79 / 100 + 2 * s.re / 3) ^ 2 * 122624409600 ^ 2 * ((s.re - 1) ^ 2 + s.im ^ 2) := by
    rw [mul_pow, mul_pow, hsq (s - 1)]
    simp
    ring
  rw [e1, hsq P, hPre, hPim]
  exact box_ten_two_poly s.re s.im h0.le h1.le ht0.le ht1

/-- The remainder factor: `‖s‖ ⋯ ‖s+7‖ ≤ 44690313818` on the box. Proved. -/
lemma prod_ten_two_le (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 39 / 4 < s.im)
    (ht1 : s.im ≤ 10) :
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ * ‖s + 7‖ * ‖s + 8‖ * ‖s + 9‖ ≤ 44690313818 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have ht2 : s.im ^ 2 ≤ 100 := by nlinarith
  have n0 : ‖s‖ ^ 2 ≤ 1616 / 16 := by
    rw [hsq]; nlinarith
  have n1 : ‖s + 1‖ ^ 2 ≤ 1664 / 16 := by
    rw [hsq]; simp only [add_re, one_re, add_im, one_im]; nlinarith
  have n2 : ‖s + 2‖ ^ 2 ≤ 1744 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n3 : ‖s + 3‖ ^ 2 ≤ 1856 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n4 : ‖s + 4‖ ^ 2 ≤ 2000 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n5 : ‖s + 5‖ ^ 2 ≤ 2176 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n6 : ‖s + 6‖ ^ 2 ≤ 2384 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n7 : ‖s + 7‖ ^ 2 ≤ 2624 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n8 : ‖s + 8‖ ^ 2 ≤ 2896 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have n9 : ‖s + 9‖ ^ 2 ≤ 3200 / 16 := by
    rw [hsq]; simp only [add_re, add_im, re_ofNat, im_ofNat]; nlinarith
  have hsq' : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ * ‖s + 7‖ * ‖s + 8‖ * ‖s + 9‖) ^ 2 ≤ (1616 / 16) * (1664 / 16) * (1744 / 16) * (1856 / 16) * (2000 / 16) * (2176 / 16) * (2384 / 16) * (2624 / 16) * (2896 / 16) * (3200 / 16) := by
    have e : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ * ‖s + 7‖ * ‖s + 8‖ * ‖s + 9‖) ^ 2 = ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 * ‖s + 2‖ ^ 2 * ‖s + 3‖ ^ 2 * ‖s + 4‖ ^ 2 * ‖s + 5‖ ^ 2 * ‖s + 6‖ ^ 2 * ‖s + 7‖ ^ 2 * ‖s + 8‖ ^ 2 * ‖s + 9‖ ^ 2 := by ring
    rw [e]
    have q1 := mul_le_mul n0 n1 (by positivity) (by norm_num)
    have q2 := mul_le_mul q1 n2 (by positivity) (by norm_num)
    have q3 := mul_le_mul q2 n3 (by positivity) (by norm_num)
    have q4 := mul_le_mul q3 n4 (by positivity) (by norm_num)
    have q5 := mul_le_mul q4 n5 (by positivity) (by norm_num)
    have q6 := mul_le_mul q5 n6 (by positivity) (by norm_num)
    have q7 := mul_le_mul q6 n7 (by positivity) (by norm_num)
    have q8 := mul_le_mul q7 n8 (by positivity) (by norm_num)
    exact mul_le_mul q8 n9 (by positivity) (by norm_num)
  have : (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ * ‖s + 7‖ * ‖s + 8‖ * ‖s + 9‖) ^ 2 ≤ 44690313818 ^ 2 := by
    refine hsq'.trans ?_; norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).mp this

/-- PROVED: `ζ` has no zero with `0 < Re ρ < 1` and `39/4 < Im ρ ≤ 10`, same argument as
`Feed1122ZetaBaseTwoEight.riemannZeta_ne_zero_nineteen_half_thirtynine_quarter` with five terms. -/
theorem riemannZeta_ne_zero_thirtynine_quarter_ten (ρ : ℂ) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (ht0 : 39 / 4 < ρ.im) (ht1 : ρ.im ≤ 10) : riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hEM := riemannZeta_eq_EM10_two h0 hρ1
  set I := ∫ x in Ioi (2 : ℝ), ((((Int.fract x) ^ 10 - 5 * (Int.fract x) ^ 9 + 15 / 2 * (Int.fract x) ^ 8 - 7 * (Int.fract x) ^ 6 + 5 * (Int.fract x) ^ 4 - 3 / 2 * (Int.fract x) ^ 2 + 5 / 66) / 1814400 : ℝ) : ℂ) * (x : ℂ) ^ (-ρ - 10) with hI
  set H := 1 / 2 + 2 / (ρ - 1) + ρ / 24 - ρ * (ρ + 1) * (ρ + 2) / 5760 + ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) / 967680 - ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) * (ρ + 6) / 154828800 + ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) * (ρ + 6) * (ρ + 7) * (ρ + 8) / 24524881920 with hH
  set Q := ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) * (ρ + 6) * (ρ + 7) * (ρ + 8) * (ρ + 9) / 2 * I with hQ
  have hkey : (2 : ℂ) ^ (-ρ) * H = Q - 1 := by
    rw [hz] at hEM; linear_combination -hEM
  have hIle : ‖I‖ ≤ 1 / 23950080 * (2 : ℝ) ^ ((-ρ - 10).re + 1) / (-(-ρ - 10).re - 1) :=
    norm_weight_int_le2 (by fun_prop) abs_B10_le (by simp; linarith)
  have hre1 : (-ρ - 10).re + 1 = -ρ.re - 9 := by simp; ring
  have hre2 : (-(-ρ - 10).re - 1) = ρ.re + 9 := by simp; ring
  rw [hre1, hre2] at hIle
  have hn2 : ‖(2 : ℂ) ^ (-ρ)‖ = (2 : ℝ) ^ (-ρ.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (-ρ)
    simpa using this
  have hP := prod_ten_two_le ρ h0 h1 ht0 ht1
  have hσ : 0 < ρ.re + 9 := by linarith
  have hQle : ‖Q‖ ≤ 44690313818 / 2 * (1 / 23950080 * (2 : ℝ) ^ (-ρ.re - 9) / (ρ.re + 9)) := by
    rw [hQ, norm_mul, norm_div, Complex.norm_ofNat, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    have hIn : 0 ≤ ‖I‖ := norm_nonneg _
    calc ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ * ‖ρ + 6‖ * ‖ρ + 7‖ * ‖ρ + 8‖ * ‖ρ + 9‖ / 2 * ‖I‖
        ≤ 44690313818 / 2 * ‖I‖ := by
          apply mul_le_mul_of_nonneg_right _ hIn; linarith
      _ ≤ 44690313818 / 2 * (1 / 23950080 * (2 : ℝ) ^ (-ρ.re - 9) / (ρ.re + 9)) :=
          mul_le_mul_of_nonneg_left hIle (by norm_num)
  have hsplit : (2 : ℝ) ^ (-ρ.re - 9) = (2 : ℝ) ^ (-ρ.re) / 512 := by
    rw [sub_eq_add_neg, Real.rpow_add two_pos]
    rw [show (-(9 : ℝ)) = ((-9 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
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
  have hE : (2 : ℝ) ^ ρ.re * ‖Q‖ ≤ 21 / 100 := by
    have := mul_le_mul_of_nonneg_left hQle hupos.le
    rw [hsplit] at this
    have e : (2 : ℝ) ^ ρ.re * (44690313818 / 2 * (1 / 23950080 * ((2 : ℝ) ^ (-ρ.re) / 512) / (ρ.re + 9))) =
        44690313818 / 24524881920 / (ρ.re + 9) * ((2 : ℝ) ^ ρ.re * (2 : ℝ) ^ (-ρ.re)) := by
      field_simp
      ring
    rw [e, hu, mul_one] at this
    have : 44690313818 / 24524881920 / (ρ.re + 9) ≤ 21 / 100 := by
      rw [div_le_iff₀ hσ]; nlinarith
    linarith
  have hH2 : (2 : ℝ) ^ ρ.re - 21 / 100 ≤ ‖H‖ := by
    have := mul_le_mul_of_nonneg_left hlow hupos.le
    have e : (2 : ℝ) ^ ρ.re * ((2 : ℝ) ^ (-ρ.re) * ‖H‖) = ‖H‖ := by
      rw [← mul_assoc, hu, one_mul]
    rw [e, mul_sub, mul_one] at this
    linarith
  have hlo := two_rpow_ge ρ.re h0.le
  have hup := main_ten_two_lt ρ h0 h1 ht0 ht1
  rw [← hH] at hup
  linarith

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], and the
first zero tables of `ζ`, Gram 1903 and Backlund 1914, read on the window `(10, 21/2]`: no zero
of `ζ` in the open strip has ordinate in `(10, 21/2]`. Class MEDIUM: the route of this file with
six Bernoulli terms; with the crude constant error bound six terms reach about `41/4` only, so
the last piece needs the exact error or a finer split, S137 numerics. -/
theorem zeta_zero_free_ten_ten_half (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : 10 < ρ.im) : 21 / 2 < ρ.im := by
  sorry

/-- `Feed1122ZetaBaseTwoEight.zeta_zero_free_thirtynine_quarter_ten_half`, exactly its statement, from
the proved range `(39/4, 10]` and the MEDIUM leaf on `(10, 21/2]`. -/
theorem zeta_zero_free_thirtynine_quarter_ten_half_s137 (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : 39 / 4 < ρ.im) : 21 / 2 < ρ.im := by
  by_cases h : ρ.im ≤ 10
  · exact absurd h0 (riemannZeta_ne_zero_thirtynine_quarter_ten ρ hre0 hre1 him h)
  · exact zeta_zero_free_ten_ten_half ρ h0 hre0 hre1 (not_le.mp h)

end LeanLab.HelfgottMajor.Feed1122ZetaBaseTwoTen

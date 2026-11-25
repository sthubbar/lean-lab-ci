import LeanLab.HelfgottMajor.Feed1122ZetaSplitTen

/-!
# Split of `zeta_zero_free_seven_half_ten_half` at height `8`, burst 20261122 S137

`Feed1122ZetaSplitTen` leaves the MEDIUM LEAF `zeta_zero_free_seven_half_ten_half`: no zero of
`ζ` in the open strip has ordinate in `(15/2, 21/2]`, Helfgott arXiv 1305.2897v4 Section 4.6
page 56 with Platt's verification and the first zero tables of Gram 1903 and Backlund 1914.

The proved three term Euler Maclaurin formula `Feed1122ZetaEM6.riemannZeta_eq_EM6`, Edwards
1974 Chapter 6, still separates `ζ` from `0` up to height `8`; the box polynomial needs sixteen
pieces in `x = t²` on `[225/4, 64]`, each bounded monomial by monomial as in `Feed1122ZetaEM6`.

* PROVED `coeff8_pos`, `box8_poly_pos`, `zeta_box_seven_half_eight_ineq`,
  `riemannZeta_ne_zero_seven_half_eight`: no zero with ordinate in `(15/2, 8]`.
* LEAF MEDIUM `zeta_zero_free_eight_ten_half`: no zero with ordinate in `(8, 21/2]`, by the
  phase free route of the `Feed1122ZetaSplitTen` header.
* PROVED assembly `zeta_zero_free_seven_half_ten_half_s137`, exactly the statement of
  `Feed1122ZetaSplitTen.zeta_zero_free_seven_half_ten_half`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ZetaEight
open Complex Set MeasureTheory LeanLab.HelfgottMajor.Feed1122ZetaEM4
  LeanLab.HelfgottMajor.Feed1122ZetaEM6

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_0 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (225 / 4 : ℝ) ≤ x) (hb : x ≤ (3631 / 64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (3631 / 64 : ℝ) := by
    calc x ^ 1 ≤ (3631 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (225 / 4 : ℝ) ≤ x ^ 1 := by
    calc (225 / 4 : ℝ) = (225 / 4 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (13184161 / 4096 : ℝ) := by
    calc x ^ 2 ≤ (3631 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (50625 / 16 : ℝ) ≤ x ^ 2 := by
    calc (50625 / 16 : ℝ) = (225 / 4 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (47871688591 / 262144 : ℝ) := by
    calc x ^ 3 ≤ (3631 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (11390625 / 64 : ℝ) ≤ x ^ 3 := by
    calc (11390625 / 64 : ℝ) = (225 / 4 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (173822101273921 / 16777216 : ℝ) := by
    calc x ^ 4 ≤ (3631 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (2562890625 / 256 : ℝ) ≤ x ^ 4 := by
    calc (2562890625 / 256 : ℝ) = (225 / 4 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (631148049725607151 / 1073741824 : ℝ) := by
    calc x ^ 5 ≤ (3631 / 64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (576650390625 / 1024 : ℝ) ≤ x ^ 5 := by
    calc (576650390625 / 1024 : ℝ) = (225 / 4 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (2291698568553679565281 / 68719476736 : ℝ) := by
    calc x ^ 6 ≤ (3631 / 64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (129746337890625 / 4096 : ℝ) ≤ x ^ 6 := by
    calc (129746337890625 / 4096 : ℝ) = (225 / 4 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (8321157502418410501535311 / 4398046511104 : ℝ) := by
    calc x ^ 7 ≤ (3631 / 64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (29192926025390625 / 16384 : ℝ) ≤ x ^ 7 := by
    calc (29192926025390625 / 16384 : ℝ) = (225 / 4 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (13027553 / 4096 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(13027553 / 4096 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1704816922531 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1267957402994 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-146532083062 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-146532083062 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-116850738082 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-116850738082 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-39566972809 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-39566972809 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-6850338988 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-6850338988 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-930809469 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-930809469 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-86032470 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-86032470 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-7607106 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-7607106 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-548719 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-548719 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-49107 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-49107 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2786 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2786 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
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
/-- Certificate piece, proved. -/
lemma coeff8_pos_1 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (3631 / 64 : ℝ) ≤ x) (hb : x ≤ (1831 / 32 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (1831 / 32 : ℝ) := by
    calc x ^ 1 ≤ (1831 / 32 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (3631 / 64 : ℝ) ≤ x ^ 1 := by
    calc (3631 / 64 : ℝ) = (3631 / 64 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (3352561 / 1024 : ℝ) := by
    calc x ^ 2 ≤ (1831 / 32 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (13184161 / 4096 : ℝ) ≤ x ^ 2 := by
    calc (13184161 / 4096 : ℝ) = (3631 / 64 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (6138539191 / 32768 : ℝ) := by
    calc x ^ 3 ≤ (1831 / 32 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (47871688591 / 262144 : ℝ) ≤ x ^ 3 := by
    calc (47871688591 / 262144 : ℝ) = (3631 / 64 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (11239665258721 / 1048576 : ℝ) := by
    calc x ^ 4 ≤ (1831 / 32 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (173822101273921 / 16777216 : ℝ) ≤ x ^ 4 := by
    calc (173822101273921 / 16777216 : ℝ) = (3631 / 64 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (20579827088718151 / 33554432 : ℝ) := by
    calc x ^ 5 ≤ (1831 / 32 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (631148049725607151 / 1073741824 : ℝ) ≤ x ^ 5 := by
    calc (631148049725607151 / 1073741824 : ℝ) = (3631 / 64 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (37681663399442934481 / 1073741824 : ℝ) := by
    calc x ^ 6 ≤ (1831 / 32 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (2291698568553679565281 / 68719476736 : ℝ) ≤ x ^ 6 := by
    calc (2291698568553679565281 / 68719476736 : ℝ) = (3631 / 64 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (68995125684380013034711 / 34359738368 : ℝ) := by
    calc x ^ 7 ≤ (1831 / 32 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (8321157502418410501535311 / 4398046511104 : ℝ) ≤ x ^ 7 := by
    calc (8321157502418410501535311 / 4398046511104 : ℝ) = (3631 / 64 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (3328785 / 1024 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(3328785 / 1024 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1680033531015 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1288291608287 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-158507660073 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-158507660073 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-120660610472 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-120660610472 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-40607924599 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-40607924599 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-6993212483 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-6993212483 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-949188815 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-949188815 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-87556181 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-87556181 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-7747924 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-7747924 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-556605 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-556605 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-49623 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-49623 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2794 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2794 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-142 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-142 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_2 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (1831 / 32 : ℝ) ≤ x) (hb : x ≤ (3693 / 64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (3693 / 64 : ℝ) := by
    calc x ^ 1 ≤ (3693 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (1831 / 32 : ℝ) ≤ x ^ 1 := by
    calc (1831 / 32 : ℝ) = (1831 / 32 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (13638249 / 4096 : ℝ) := by
    calc x ^ 2 ≤ (3693 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (3352561 / 1024 : ℝ) ≤ x ^ 2 := by
    calc (3352561 / 1024 : ℝ) = (1831 / 32 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (50366053557 / 262144 : ℝ) := by
    calc x ^ 3 ≤ (3693 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (6138539191 / 32768 : ℝ) ≤ x ^ 3 := by
    calc (6138539191 / 32768 : ℝ) = (1831 / 32 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (186001835786001 / 16777216 : ℝ) := by
    calc x ^ 4 ≤ (3693 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (11239665258721 / 1048576 : ℝ) ≤ x ^ 4 := by
    calc (11239665258721 / 1048576 : ℝ) = (1831 / 32 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (686904779557701693 / 1073741824 : ℝ) := by
    calc x ^ 5 ≤ (3693 / 64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (20579827088718151 / 33554432 : ℝ) ≤ x ^ 5 := by
    calc (20579827088718151 / 33554432 : ℝ) = (1831 / 32 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (2536739350906592352249 / 68719476736 : ℝ) := by
    calc x ^ 6 ≤ (3693 / 64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (37681663399442934481 / 1073741824 : ℝ) ≤ x ^ 6 := by
    calc (37681663399442934481 / 1073741824 : ℝ) = (1831 / 32 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (9368178422898045556855557 / 4398046511104 : ℝ) := by
    calc x ^ 7 ≤ (3693 / 64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (68995125684380013034711 / 34359738368 : ℝ) ≤ x ^ 7 := by
    calc (68995125684380013034711 / 34359738368 : ℝ) = (1831 / 32 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (13604649 / 4096 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(13604649 / 4096 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1650527682916 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1308448056883 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-171030143806 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-171030143806 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-124568733390 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-124568733390 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-41671715359 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-41671715359 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-7138406390 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-7138406390 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-967857322 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-967857322 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-89097679 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-89097679 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-7890289 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-7890289 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-564533 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-564533 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-50143 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-50143 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2803 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2803 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-142 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-142 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_3 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (3693 / 64 : ℝ) ≤ x) (hb : x ≤ (931 / 16 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (931 / 16 : ℝ) := by
    calc x ^ 1 ≤ (931 / 16 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (3693 / 64 : ℝ) ≤ x ^ 1 := by
    calc (3693 / 64 : ℝ) = (3693 / 64 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (866761 / 256 : ℝ) := by
    calc x ^ 2 ≤ (931 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (13638249 / 4096 : ℝ) ≤ x ^ 2 := by
    calc (13638249 / 4096 : ℝ) = (3693 / 64 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (806954491 / 4096 : ℝ) := by
    calc x ^ 3 ≤ (931 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (50366053557 / 262144 : ℝ) ≤ x ^ 3 := by
    calc (50366053557 / 262144 : ℝ) = (3693 / 64 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (751274631121 / 65536 : ℝ) := by
    calc x ^ 4 ≤ (931 / 16 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (186001835786001 / 16777216 : ℝ) ≤ x ^ 4 := by
    calc (186001835786001 / 16777216 : ℝ) = (3693 / 64 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (699436681573651 / 1048576 : ℝ) := by
    calc x ^ 5 ≤ (931 / 16 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (686904779557701693 / 1073741824 : ℝ) ≤ x ^ 5 := by
    calc (686904779557701693 / 1073741824 : ℝ) = (3693 / 64 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (651175550545069081 / 16777216 : ℝ) := by
    calc x ^ 6 ≤ (931 / 16 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (2536739350906592352249 / 68719476736 : ℝ) ≤ x ^ 6 := by
    calc (2536739350906592352249 / 68719476736 : ℝ) = (3693 / 64 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (606244437557459314411 / 268435456 : ℝ) := by
    calc x ^ 7 ≤ (931 / 16 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (9368178422898045556855557 / 4398046511104 : ℝ) ≤ x ^ 7 := by
    calc (9368178422898045556855557 / 4398046511104 : ℝ) = (3693 / 64 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (868505 / 256 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(868505 / 256 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1616028635086 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1328401103824 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-184117874240 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-184117874240 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-128577190047 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-128577190047 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-42758778909 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-42758778909 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-7285950638 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-7285950638 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-986818631 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-986818631 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-90657087 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-90657087 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-8034212 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-8034212 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-572503 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-572503 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-50665 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-50665 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2812 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2812 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-143 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-143 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_4 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (931 / 16 : ℝ) ≤ x) (hb : x ≤ (3755 / 64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (3755 / 64 : ℝ) := by
    calc x ^ 1 ≤ (3755 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (931 / 16 : ℝ) ≤ x ^ 1 := by
    calc (931 / 16 : ℝ) = (931 / 16 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (14100025 / 4096 : ℝ) := by
    calc x ^ 2 ≤ (3755 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (866761 / 256 : ℝ) ≤ x ^ 2 := by
    calc (866761 / 256 : ℝ) = (931 / 16 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (52945593875 / 262144 : ℝ) := by
    calc x ^ 3 ≤ (3755 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (806954491 / 4096 : ℝ) ≤ x ^ 3 := by
    calc (806954491 / 4096 : ℝ) = (931 / 16 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (198810705000625 / 16777216 : ℝ) := by
    calc x ^ 4 ≤ (3755 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (751274631121 / 65536 : ℝ) ≤ x ^ 4 := by
    calc (751274631121 / 65536 : ℝ) = (931 / 16 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (746534197277346875 / 1073741824 : ℝ) := by
    calc x ^ 5 ≤ (3755 / 64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (699436681573651 / 1048576 : ℝ) ≤ x ^ 5 := by
    calc (699436681573651 / 1048576 : ℝ) = (931 / 16 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (2803235910776437515625 / 68719476736 : ℝ) := by
    calc x ^ 6 ≤ (3755 / 64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (651175550545069081 / 16777216 : ℝ) ≤ x ^ 6 := by
    calc (651175550545069081 / 16777216 : ℝ) = (931 / 16 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (10526150844965522871171875 / 4398046511104 : ℝ) := by
    calc x ^ 7 ≤ (3755 / 64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (606244437557459314411 / 268435456 : ℝ) ≤ x ^ 7 := by
    calc (606244437557459314411 / 268435456 : ℝ) = (931 / 16 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (14189433 / 4096 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(14189433 / 4096 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1576255605912 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1348124170238 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-197789641986 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-197789641986 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-132688097024 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-132688097024 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-43869555389 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-43869555389 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-7435875393 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-7435875393 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1006076409 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1006076409 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-92234527 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-92234527 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-8179703 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-8179703 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-580515 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-580515 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-51190 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-51190 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2821 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2821 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-143 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-143 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_5 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (3755 / 64 : ℝ) ≤ x) (hb : x ≤ (1893 / 32 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (1893 / 32 : ℝ) := by
    calc x ^ 1 ≤ (1893 / 32 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (3755 / 64 : ℝ) ≤ x ^ 1 := by
    calc (3755 / 64 : ℝ) = (3755 / 64 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (3583449 / 1024 : ℝ) := by
    calc x ^ 2 ≤ (1893 / 32 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (14100025 / 4096 : ℝ) ≤ x ^ 2 := by
    calc (14100025 / 4096 : ℝ) = (3755 / 64 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (6783468957 / 32768 : ℝ) := by
    calc x ^ 3 ≤ (1893 / 32 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (52945593875 / 262144 : ℝ) ≤ x ^ 3 := by
    calc (52945593875 / 262144 : ℝ) = (3755 / 64 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (12841106735601 / 1048576 : ℝ) := by
    calc x ^ 4 ≤ (1893 / 32 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (198810705000625 / 16777216 : ℝ) ≤ x ^ 4 := by
    calc (198810705000625 / 16777216 : ℝ) = (3755 / 64 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (24308215050492693 / 33554432 : ℝ) := by
    calc x ^ 5 ≤ (1893 / 32 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (746534197277346875 / 1073741824 : ℝ) ≤ x ^ 5 := by
    calc (746534197277346875 / 1073741824 : ℝ) = (3755 / 64 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (46015451090582667849 / 1073741824 : ℝ) := by
    calc x ^ 6 ≤ (1893 / 32 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (2803235910776437515625 / 68719476736 : ℝ) ≤ x ^ 6 := by
    calc (2803235910776437515625 / 68719476736 : ℝ) = (3755 / 64 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (87107248914472990238157 / 34359738368 : ℝ) := by
    calc x ^ 7 ≤ (1893 / 32 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (10526150844965522871171875 / 4398046511104 : ℝ) ≤ x ^ 7 := by
    calc (10526150844965522871171875 / 4398046511104 : ℝ) = (3755 / 64 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (3621177 / 1024 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(3621177 / 1024 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1530917520975 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1367589724855 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-212064695503 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-212064695503 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-136903604557 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-136903604557 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-45004491313 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-45004491313 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-7588211058 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-7588211058 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1025634349 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1025634349 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-93830122 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-93830122 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-8326772 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-8326772 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-588569 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-588569 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-51718 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-51718 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2829 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2829 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-144 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-144 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_6 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (1893 / 32 : ℝ) ≤ x) (hb : x ≤ (3817 / 64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (3817 / 64 : ℝ) := by
    calc x ^ 1 ≤ (3817 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (1893 / 32 : ℝ) ≤ x ^ 1 := by
    calc (1893 / 32 : ℝ) = (1893 / 32 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (14569489 / 4096 : ℝ) := by
    calc x ^ 2 ≤ (3817 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (3583449 / 1024 : ℝ) ≤ x ^ 2 := by
    calc (3583449 / 1024 : ℝ) = (1893 / 32 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (55611739513 / 262144 : ℝ) := by
    calc x ^ 3 ≤ (3817 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (6783468957 / 32768 : ℝ) ≤ x ^ 3 := by
    calc (6783468957 / 32768 : ℝ) = (1893 / 32 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (212270009721121 / 16777216 : ℝ) := by
    calc x ^ 4 ≤ (3817 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (12841106735601 / 1048576 : ℝ) ≤ x ^ 4 := by
    calc (12841106735601 / 1048576 : ℝ) = (1893 / 32 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (810234627105518857 / 1073741824 : ℝ) := by
    calc x ^ 5 ≤ (3817 / 64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (24308215050492693 / 33554432 : ℝ) ≤ x ^ 5 := by
    calc (24308215050492693 / 33554432 : ℝ) = (1893 / 32 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (3092665571661765477169 / 68719476736 : ℝ) := by
    calc x ^ 6 ≤ (3817 / 64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (46015451090582667849 / 1073741824 : ℝ) ≤ x ^ 6 := by
    calc (46015451090582667849 / 1073741824 : ℝ) = (1893 / 32 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (11804704487032958826354073 / 4398046511104 : ℝ) := by
    calc x ^ 7 ≤ (3817 / 64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (87107248914472990238157 / 34359738368 : ℝ) ≤ x ^ 7 := by
    calc (87107248914472990238157 / 34359738368 : ℝ) = (1893 / 32 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (14781905 / 4096 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(14781905 / 4096 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1479712754628 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1386769265352 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-226962748379 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-226962748379 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-141225896830 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-141225896830 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-46164039609 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-46164039609 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-7742988275 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-7742988275 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1045496170 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1045496170 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-95443995 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-95443995 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-8475430 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-8475430 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-596666 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-596666 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-52249 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-52249 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2838 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2838 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-144 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-144 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_7 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (3817 / 64 : ℝ) ≤ x) (hb : x ≤ (481 / 8 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (481 / 8 : ℝ) := by
    calc x ^ 1 ≤ (481 / 8 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (3817 / 64 : ℝ) ≤ x ^ 1 := by
    calc (3817 / 64 : ℝ) = (3817 / 64 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (231361 / 64 : ℝ) := by
    calc x ^ 2 ≤ (481 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (14569489 / 4096 : ℝ) ≤ x ^ 2 := by
    calc (14569489 / 4096 : ℝ) = (3817 / 64 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (111284641 / 512 : ℝ) := by
    calc x ^ 3 ≤ (481 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (55611739513 / 262144 : ℝ) ≤ x ^ 3 := by
    calc (55611739513 / 262144 : ℝ) = (3817 / 64 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (53527912321 / 4096 : ℝ) := by
    calc x ^ 4 ≤ (481 / 8 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (212270009721121 / 16777216 : ℝ) ≤ x ^ 4 := by
    calc (212270009721121 / 16777216 : ℝ) = (3817 / 64 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (25746925826401 / 32768 : ℝ) := by
    calc x ^ 5 ≤ (481 / 8 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (810234627105518857 / 1073741824 : ℝ) ≤ x ^ 5 := by
    calc (810234627105518857 / 1073741824 : ℝ) = (3817 / 64 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (12384271322498881 / 262144 : ℝ) := by
    calc x ^ 6 ≤ (481 / 8 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (3092665571661765477169 / 68719476736 : ℝ) ≤ x ^ 6 := by
    calc (3092665571661765477169 / 68719476736 : ℝ) = (3817 / 64 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (5956834506121961761 / 2097152 : ℝ) := by
    calc x ^ 7 ≤ (481 / 8 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (11804704487032958826354073 / 4398046511104 : ℝ) ≤ x ^ 7 := by
    calc (11804704487032958826354073 / 4398046511104 : ℝ) = (3817 / 64 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (235641 / 64 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(235641 / 64 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1422328867467 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1405633299531 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-242503986665 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-242503986665 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-145657192256 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-145657192256 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-47348659676 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-47348659676 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-7900237923 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-7900237923 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1065665619 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1065665619 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-97076269 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-97076269 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-8625686 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-8625686 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-604805 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-604805 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-52782 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-52782 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2847 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2847 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-145 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-145 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_8 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (481 / 8 : ℝ) ≤ x) (hb : x ≤ (3879 / 64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (3879 / 64 : ℝ) := by
    calc x ^ 1 ≤ (3879 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (481 / 8 : ℝ) ≤ x ^ 1 := by
    calc (481 / 8 : ℝ) = (481 / 8 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (15046641 / 4096 : ℝ) := by
    calc x ^ 2 ≤ (3879 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (231361 / 64 : ℝ) ≤ x ^ 2 := by
    calc (231361 / 64 : ℝ) = (481 / 8 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (58365920439 / 262144 : ℝ) := by
    calc x ^ 3 ≤ (3879 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (111284641 / 512 : ℝ) ≤ x ^ 3 := by
    calc (111284641 / 512 : ℝ) = (481 / 8 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (226401405382881 / 16777216 : ℝ) := by
    calc x ^ 4 ≤ (3879 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (53527912321 / 4096 : ℝ) ≤ x ^ 4 := by
    calc (53527912321 / 4096 : ℝ) = (481 / 8 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (878211051480195399 / 1073741824 : ℝ) := by
    calc x ^ 5 ≤ (3879 / 64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (25746925826401 / 32768 : ℝ) ≤ x ^ 5 := by
    calc (25746925826401 / 32768 : ℝ) = (481 / 8 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (3406580668691677952721 / 68719476736 : ℝ) := by
    calc x ^ 6 ≤ (3879 / 64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (12384271322498881 / 262144 : ℝ) ≤ x ^ 6 := by
    calc (12384271322498881 / 262144 : ℝ) = (481 / 8 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (13214126413855018778604759 / 4398046511104 : ℝ) := by
    calc x ^ 7 ≤ (3879 / 64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (5956834506121961761 / 2097152 : ℝ) ≤ x ^ 7 := by
    calc (5956834506121961761 / 2097152 : ℝ) = (481 / 8 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (15382065 / 4096 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(15382065 / 4096 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1358442339665 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1424151326325 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-258709076259 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-258709076259 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-150199743773 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-150199743773 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-48558817425 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-48558817425 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-8059991120 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-8059991120 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1086146468 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1086146468 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-98727066 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-98727066 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-8777551 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-8777551 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-612986 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-612986 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-53319 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-53319 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2855 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2855 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-145 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-145 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_9 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (3879 / 64 : ℝ) ≤ x) (hb : x ≤ (1955 / 32 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (1955 / 32 : ℝ) := by
    calc x ^ 1 ≤ (1955 / 32 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (3879 / 64 : ℝ) ≤ x ^ 1 := by
    calc (3879 / 64 : ℝ) = (3879 / 64 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (3822025 / 1024 : ℝ) := by
    calc x ^ 2 ≤ (1955 / 32 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (15046641 / 4096 : ℝ) ≤ x ^ 2 := by
    calc (15046641 / 4096 : ℝ) = (3879 / 64 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (7472058875 / 32768 : ℝ) := by
    calc x ^ 3 ≤ (1955 / 32 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (58365920439 / 262144 : ℝ) ≤ x ^ 3 := by
    calc (58365920439 / 262144 : ℝ) = (3879 / 64 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (14607875100625 / 1048576 : ℝ) := by
    calc x ^ 4 ≤ (1955 / 32 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (226401405382881 / 16777216 : ℝ) ≤ x ^ 4 := by
    calc (226401405382881 / 16777216 : ℝ) = (3879 / 64 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (28558395821721875 / 33554432 : ℝ) := by
    calc x ^ 5 ≤ (1955 / 32 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (878211051480195399 / 1073741824 : ℝ) ≤ x ^ 5 := by
    calc (878211051480195399 / 1073741824 : ℝ) = (3879 / 64 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (55831663831466265625 / 1073741824 : ℝ) := by
    calc x ^ 6 ≤ (1955 / 32 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (3406580668691677952721 / 68719476736 : ℝ) ≤ x ^ 6 := by
    calc (3406580668691677952721 / 68719476736 : ℝ) = (3879 / 64 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (109150902790516549296875 / 34359738368 : ℝ) := by
    calc x ^ 7 ≤ (1955 / 32 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (13214126413855018778604759 / 4398046511104 : ℝ) ≤ x ^ 7 := by
    calc (13214126413855018778604759 / 4398046511104 : ℝ) = (3879 / 64 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (3921257 / 1024 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(3921257 / 1024 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1287718300135 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1442291816649 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-275599170357 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-275599170357 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-154855839125 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-154855839125 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-49794985328 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-49794985328 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-8222279221 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-8222279221 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1106942516 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1106942516 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-100396510 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-100396510 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-8931035 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-8931035 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-621209 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-621209 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-53858 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-53858 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2864 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2864 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-146 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-146 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_10 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (1955 / 32 : ℝ) ≤ x) (hb : x ≤ (3941 / 64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (3941 / 64 : ℝ) := by
    calc x ^ 1 ≤ (3941 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (1955 / 32 : ℝ) ≤ x ^ 1 := by
    calc (1955 / 32 : ℝ) = (1955 / 32 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (15531481 / 4096 : ℝ) := by
    calc x ^ 2 ≤ (3941 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (3822025 / 1024 : ℝ) ≤ x ^ 2 := by
    calc (3822025 / 1024 : ℝ) = (1955 / 32 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (61209566621 / 262144 : ℝ) := by
    calc x ^ 3 ≤ (3941 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (7472058875 / 32768 : ℝ) ≤ x ^ 3 := by
    calc (7472058875 / 32768 : ℝ) = (1955 / 32 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (241226902053361 / 16777216 : ℝ) := by
    calc x ^ 4 ≤ (3941 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (14607875100625 / 1048576 : ℝ) ≤ x ^ 4 := by
    calc (14607875100625 / 1048576 : ℝ) = (1955 / 32 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (950675220992295701 / 1073741824 : ℝ) := by
    calc x ^ 5 ≤ (3941 / 64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (28558395821721875 / 33554432 : ℝ) ≤ x ^ 5 := by
    calc (28558395821721875 / 33554432 : ℝ) = (1955 / 32 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (3746611045930637357641 / 68719476736 : ℝ) := by
    calc x ^ 6 ≤ (3941 / 64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (55831663831466265625 / 1073741824 : ℝ) ≤ x ^ 6 := by
    calc (55831663831466265625 / 1073741824 : ℝ) = (1955 / 32 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (14765394132012641826463181 / 4398046511104 : ℝ) := by
    calc x ^ 7 ≤ (3941 / 64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (109150902790516549296875 / 34359738368 : ℝ) ≤ x ^ 7 := by
    calc (109150902790516549296875 / 34359738368 : ℝ) = (1955 / 32 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (15989913 / 4096 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(15989913 / 4096 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1209810251495 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1460022194070 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-293195916949 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-293195916949 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-159627801154 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-159627801154 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-51057642471 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-51057642471 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-8387133818 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-8387133818 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1128057588 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1128057588 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-102084722 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-102084722 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-9086148 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-9086148 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-629475 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-629475 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-54400 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-54400 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2873 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2873 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-146 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-146 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_11 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (3941 / 64 : ℝ) ≤ x) (hb : x ≤ (993 / 16 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (993 / 16 : ℝ) := by
    calc x ^ 1 ≤ (993 / 16 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (3941 / 64 : ℝ) ≤ x ^ 1 := by
    calc (3941 / 64 : ℝ) = (3941 / 64 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (986049 / 256 : ℝ) := by
    calc x ^ 2 ≤ (993 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (15531481 / 4096 : ℝ) ≤ x ^ 2 := by
    calc (15531481 / 4096 : ℝ) = (3941 / 64 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (979146657 / 4096 : ℝ) := by
    calc x ^ 3 ≤ (993 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (61209566621 / 262144 : ℝ) ≤ x ^ 3 := by
    calc (61209566621 / 262144 : ℝ) = (3941 / 64 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (972292630401 / 65536 : ℝ) := by
    calc x ^ 4 ≤ (993 / 16 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (241226902053361 / 16777216 : ℝ) ≤ x ^ 4 := by
    calc (241226902053361 / 16777216 : ℝ) = (3941 / 64 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (965486581988193 / 1048576 : ℝ) := by
    calc x ^ 5 ≤ (993 / 16 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (950675220992295701 / 1073741824 : ℝ) ≤ x ^ 5 := by
    calc (950675220992295701 / 1073741824 : ℝ) = (3941 / 64 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (958728175914275649 / 16777216 : ℝ) := by
    calc x ^ 6 ≤ (993 / 16 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (3746611045930637357641 / 68719476736 : ℝ) ≤ x ^ 6 := by
    calc (3746611045930637357641 / 68719476736 : ℝ) = (3941 / 64 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (952017078682875719457 / 268435456 : ℝ) := by
    calc x ^ 7 ≤ (993 / 16 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (14765394132012641826463181 / 4398046511104 : ℝ) ≤ x ^ 7 := by
    calc (14765394132012641826463181 / 4398046511104 : ℝ) = (3941 / 64 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (1018545 / 256 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(1018545 / 256 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1124359790788 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1477308815315 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-311521466375 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-311521466375 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-164517988087 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-164517988087 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-52347274596 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-52347274596 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-8554586743 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-8554586743 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1149495536 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1149495536 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-103791826 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-103791826 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-9242901 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-9242901 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-637783 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-637783 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-54945 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-54945 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2882 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2882 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-147 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-147 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_12 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (993 / 16 : ℝ) ≤ x) (hb : x ≤ (4003 / 64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (4003 / 64 : ℝ) := by
    calc x ^ 1 ≤ (4003 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (993 / 16 : ℝ) ≤ x ^ 1 := by
    calc (993 / 16 : ℝ) = (993 / 16 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (16024009 / 4096 : ℝ) := by
    calc x ^ 2 ≤ (4003 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (986049 / 256 : ℝ) ≤ x ^ 2 := by
    calc (986049 / 256 : ℝ) = (993 / 16 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (64144108027 / 262144 : ℝ) := by
    calc x ^ 3 ≤ (4003 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (979146657 / 4096 : ℝ) ≤ x ^ 3 := by
    calc (979146657 / 4096 : ℝ) = (993 / 16 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (256768864432081 / 16777216 : ℝ) := by
    calc x ^ 4 ≤ (4003 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (972292630401 / 65536 : ℝ) ≤ x ^ 4 := by
    calc (972292630401 / 65536 : ℝ) = (993 / 16 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (1027845764321620243 / 1073741824 : ℝ) := by
    calc x ^ 5 ≤ (4003 / 64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (965486581988193 / 1048576 : ℝ) ≤ x ^ 5 := by
    calc (965486581988193 / 1048576 : ℝ) = (993 / 16 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (4114466594579445832729 / 68719476736 : ℝ) := by
    calc x ^ 6 ≤ (4003 / 64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (958728175914275649 / 16777216 : ℝ) ≤ x ^ 6 := by
    calc (958728175914275649 / 16777216 : ℝ) = (993 / 16 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (16470209778101521668414187 / 4398046511104 : ℝ) := by
    calc x ^ 7 ≤ (4003 / 64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (952017078682875719457 / 268435456 : ℝ) ≤ x ^ 7 := by
    calc (952017078682875719457 / 268435456 : ℝ) = (993 / 16 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (16605449 / 4096 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(16605449 / 4096 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (1030996325954 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1494116950618 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-330598478943 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-330598478943 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-169528793823 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-169528793823 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-53664374152 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-53664374152 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-8724670062 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-8724670062 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1171260238 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1171260238 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-105517944 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-105517944 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-9401304 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-9401304 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-646133 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-646133 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-55493 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-55493 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2890 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2890 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-147 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-147 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_13 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (4003 / 64 : ℝ) ≤ x) (hb : x ≤ (2017 / 32 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (2017 / 32 : ℝ) := by
    calc x ^ 1 ≤ (2017 / 32 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (4003 / 64 : ℝ) ≤ x ^ 1 := by
    calc (4003 / 64 : ℝ) = (4003 / 64 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (4068289 / 1024 : ℝ) := by
    calc x ^ 2 ≤ (2017 / 32 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (16024009 / 4096 : ℝ) ≤ x ^ 2 := by
    calc (16024009 / 4096 : ℝ) = (4003 / 64 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (8205738913 / 32768 : ℝ) := by
    calc x ^ 3 ≤ (2017 / 32 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (64144108027 / 262144 : ℝ) ≤ x ^ 3 := by
    calc (64144108027 / 262144 : ℝ) = (4003 / 64 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (16550975387521 / 1048576 : ℝ) := by
    calc x ^ 4 ≤ (2017 / 32 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (256768864432081 / 16777216 : ℝ) ≤ x ^ 4 := by
    calc (256768864432081 / 16777216 : ℝ) = (4003 / 64 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (33383317356629857 / 33554432 : ℝ) := by
    calc x ^ 5 ≤ (2017 / 32 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (1027845764321620243 / 1073741824 : ℝ) ≤ x ^ 5 := by
    calc (1027845764321620243 / 1073741824 : ℝ) = (4003 / 64 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (67334151108322421569 / 1073741824 : ℝ) := by
    calc x ^ 6 ≤ (2017 / 32 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (4114466594579445832729 / 68719476736 : ℝ) ≤ x ^ 6 := by
    calc (4114466594579445832729 / 68719476736 : ℝ) = (4003 / 64 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (135812982785486324304673 / 34359738368 : ℝ) := by
    calc x ^ 7 ≤ (2017 / 32 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (16470209778101521668414187 / 4398046511104 : ℝ) ≤ x ^ 7 := by
    calc (16470209778101521668414187 / 4398046511104 : ℝ) = (4003 / 64 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (4229025 / 1024 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(4229025 / 1024 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (929336787989 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1510410763888 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-350450132587 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-350450132587 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-174662648222 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-174662648222 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-55009440343 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-55009440343 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-8897416084 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-8897416084 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1193355599 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1193355599 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-107263200 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-107263200 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-9561366 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-9561366 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-654525 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-654525 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-56043 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-56043 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2899 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2899 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-148 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-148 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_14 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (2017 / 32 : ℝ) ≤ x) (hb : x ≤ (4065 / 64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ (4065 / 64 : ℝ) := by
    calc x ^ 1 ≤ (4065 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (2017 / 32 : ℝ) ≤ x ^ 1 := by
    calc (2017 / 32 : ℝ) = (2017 / 32 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ (16524225 / 4096 : ℝ) := by
    calc x ^ 2 ≤ (4065 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (4068289 / 1024 : ℝ) ≤ x ^ 2 := by
    calc (4068289 / 1024 : ℝ) = (2017 / 32 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ (67170974625 / 262144 : ℝ) := by
    calc x ^ 3 ≤ (4065 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (8205738913 / 32768 : ℝ) ≤ x ^ 3 := by
    calc (8205738913 / 32768 : ℝ) = (2017 / 32 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ (273050011850625 / 16777216 : ℝ) := by
    calc x ^ 4 ≤ (4065 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (16550975387521 / 1048576 : ℝ) ≤ x ^ 4 := by
    calc (16550975387521 / 1048576 : ℝ) = (2017 / 32 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ (1109948298172790625 / 1073741824 : ℝ) := by
    calc x ^ 5 ≤ (4065 / 64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (33383317356629857 / 33554432 : ℝ) ≤ x ^ 5 := by
    calc (33383317356629857 / 33554432 : ℝ) = (2017 / 32 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ (4511939832072393890625 / 68719476736 : ℝ) := by
    calc x ^ 6 ≤ (4065 / 64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (67334151108322421569 / 1073741824 : ℝ) ≤ x ^ 6 := by
    calc (67334151108322421569 / 1073741824 : ℝ) = (2017 / 32 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ (18341035417374281165390625 / 4398046511104 : ℝ) := by
    calc x ^ 7 ≤ (4065 / 64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (135812982785486324304673 / 34359738368 : ℝ) ≤ x ^ 7 := by
    calc (135812982785486324304673 / 34359738368 : ℝ) = (2017 / 32 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (17228673 / 4096 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(17228673 / 4096 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (818985338788 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1526153292715 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-371100130599 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-371100130599 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-179922017392 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-179922017392 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-56382979173 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-56382979173 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-9072857350 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-9072857350 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1215785550 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1215785550 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-109027715 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-109027715 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-9723099 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-9723099 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-662960 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-662960 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-56596 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-56596 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2908 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2908 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-148 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-148 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

set_option maxHeartbeats 4000000 in
/-- Certificate piece, proved. -/
lemma coeff8_pos_15 (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (4065 / 64 : ℝ) ≤ x) (hb : x ≤ (64 : ℝ)) :
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
  have u1 : x ^ 1 ≤ 64 := by
    calc x ^ 1 ≤ (64 : ℝ) ^ 1 := pow_le_pow_left₀ hx hb 1
      _ = _ := by norm_num
  have l1 : (4065 / 64 : ℝ) ≤ x ^ 1 := by
    calc (4065 / 64 : ℝ) = (4065 / 64 : ℝ) ^ 1 := by norm_num
      _ ≤ x ^ 1 := pow_le_pow_left₀ (by norm_num) ha 1
  have u2 : x ^ 2 ≤ 4096 := by
    calc x ^ 2 ≤ (64 : ℝ) ^ 2 := pow_le_pow_left₀ hx hb 2
      _ = _ := by norm_num
  have l2 : (16524225 / 4096 : ℝ) ≤ x ^ 2 := by
    calc (16524225 / 4096 : ℝ) = (4065 / 64 : ℝ) ^ 2 := by norm_num
      _ ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have u3 : x ^ 3 ≤ 262144 := by
    calc x ^ 3 ≤ (64 : ℝ) ^ 3 := pow_le_pow_left₀ hx hb 3
      _ = _ := by norm_num
  have l3 : (67170974625 / 262144 : ℝ) ≤ x ^ 3 := by
    calc (67170974625 / 262144 : ℝ) = (4065 / 64 : ℝ) ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) ha 3
  have u4 : x ^ 4 ≤ 16777216 := by
    calc x ^ 4 ≤ (64 : ℝ) ^ 4 := pow_le_pow_left₀ hx hb 4
      _ = _ := by norm_num
  have l4 : (273050011850625 / 16777216 : ℝ) ≤ x ^ 4 := by
    calc (273050011850625 / 16777216 : ℝ) = (4065 / 64 : ℝ) ^ 4 := by norm_num
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) ha 4
  have u5 : x ^ 5 ≤ 1073741824 := by
    calc x ^ 5 ≤ (64 : ℝ) ^ 5 := pow_le_pow_left₀ hx hb 5
      _ = _ := by norm_num
  have l5 : (1109948298172790625 / 1073741824 : ℝ) ≤ x ^ 5 := by
    calc (1109948298172790625 / 1073741824 : ℝ) = (4065 / 64 : ℝ) ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) ha 5
  have u6 : x ^ 6 ≤ 68719476736 := by
    calc x ^ 6 ≤ (64 : ℝ) ^ 6 := pow_le_pow_left₀ hx hb 6
      _ = _ := by norm_num
  have l6 : (4511939832072393890625 / 68719476736 : ℝ) ≤ x ^ 6 := by
    calc (4511939832072393890625 / 68719476736 : ℝ) = (4065 / 64 : ℝ) ^ 6 := by norm_num
      _ ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
  have u7 : x ^ 7 ≤ 4398046511104 := by
    calc x ^ 7 ≤ (64 : ℝ) ^ 7 := pow_le_pow_left₀ hx hb 7
      _ = _ := by norm_num
  have l7 : (18341035417374281165390625 / 4398046511104 : ℝ) ≤ x ^ 7 := by
    calc (18341035417374281165390625 / 4398046511104 : ℝ) = (4065 / 64 : ℝ) ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) ha 7
  have hf : 0 ≤ (4283 : ℝ) - (x ^ 2 + 31 * x - 1797) := by nlinarith
  have h5 : 0 ≤ x ^ 5 := by positivity
  have hfac : -(4283 : ℝ) * x ^ 5 ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 := by
    nlinarith [mul_nonneg h5 hf]
  have hc0 : (699533074625 : ℝ) ≤ -x ^ 7 - 31 * x ^ 6 + 1797 * x ^ 5 + 156407 * x ^ 4 + 7186904 * x ^ 3 + 191571924 * x ^ 2 + 2089659600 * x + 5715360000 := by linarith
  have hc1 : (1541306428213 : ℝ) ≤ -18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000 := by linarith
  have t1 : 0 ≤ (-18 * x ^ 6 + 480 * x ^ 5 + 54786 * x ^ 4 + 2624700 * x ^ 3 + 134111052 * x ^ 2 + 2597612640 * x + 11857104000) * g :=
    mul_nonneg (by linarith) (by positivity)
  have hc2 : (-392572709406 : ℝ) ≤ -6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000 := by linarith
  have t2 : (-392572709406 : ℝ) ≤ (-6 * x ^ 6 - 171 * x ^ 5 + 7912 * x ^ 4 - 286123 * x ^ 3 + 15919168 * x ^ 2 + 1186928328 * x + 9981090000) * g ^ 2 := by
    have g0 : 0 ≤ g ^ 2 := by positivity
    have g1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) g0]
  have hc3 : (-185309403979 : ℝ) ≤ -90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840 := by linarith
  have t3 : (-185309403979 : ℝ) ≤ (-90 * x ^ 5 + 708 * x ^ 4 - 244902 * x ^ 3 - 12411588 * x ^ 2 + 165888504 * x + 4305567840) * g ^ 3 := by
    have g0 : 0 ≤ g ^ 3 := by positivity
    have g1 : g ^ 3 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc3) g0]
  have hc4 : (-57785503500 : ℝ) ≤ -15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284 := by linarith
  have t4 : (-57785503500 : ℝ) ≤ (-15 * x ^ 5 - 458 * x ^ 4 - 35686 * x ^ 3 - 5448683 * x ^ 2 - 51331096 * x + 962455284) * g ^ 4 := by
    have g0 : 0 ≤ g ^ 4 := by positivity
    have g1 : g ^ 4 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc4) g0]
  have hc5 : (-9251026644 : ℝ) ≤ -180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812 := by linarith
  have t5 : (-9251026644 : ℝ) ≤ (-180 * x ^ 4 - 2520 * x ^ 3 - 976542 * x ^ 2 - 25965276 * x + 91168812) * g ^ 5 := by
    have g0 : 0 ≤ g ^ 5 := by positivity
    have g1 : g ^ 5 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc5) g0]
  have hc6 : (-1238554048 : ℝ) ≤ -20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600 := by linarith
  have t6 : (-1238554048 : ℝ) ≤ (-20 * x ^ 4 - 742 * x ^ 3 - 95984 * x ^ 2 - 4982969 * x + 3561600) * g ^ 6 := by
    have g0 : 0 ≤ g ^ 6 := by positivity
    have g1 : g ^ 6 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc6) g0]
  have hc7 : (-110811612 : ℝ) ≤ -180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372 := by linarith
  have t7 : (-110811612 : ℝ) ≤ (-180 * x ^ 3 - 7008 * x ^ 2 - 594114 * x + 3102372) * g ^ 7 := by
    have g0 : 0 ≤ g ^ 7 := by positivity
    have g1 : g ^ 7 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc7) g0]
  have hc8 : (-9886512 : ℝ) ≤ -15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864 := by linarith
  have t8 : (-9886512 : ℝ) ≤ (-15 * x ^ 3 - 723 * x ^ 2 - 62247 * x + 990864) * g ^ 8 := by
    have g0 : 0 ≤ g ^ 8 := by positivity
    have g1 : g ^ 8 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc8) g0]
  have hc9 : (-671436 : ℝ) ≤ -90 * x ^ 2 - 6024 * x + 82740 := by linarith
  have t9 : (-671436 : ℝ) ≤ (-90 * x ^ 2 - 6024 * x + 82740) * g ^ 9 := by
    have g0 : 0 ≤ g ^ 9 := by positivity
    have g1 : g ^ 9 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc9) g0]
  have hc10 : (-57152 : ℝ) ≤ -6 * x ^ 2 - 383 * x - 8064 := by linarith
  have t10 : (-57152 : ℝ) ≤ (-6 * x ^ 2 - 383 * x - 8064) * g ^ 10 := by
    have g0 : 0 ≤ g ^ 10 := by positivity
    have g1 : g ^ 10 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc10) g0]
  have hc11 : (-2916 : ℝ) ≤ -18 * x - 1764 := by linarith
  have t11 : (-2916 : ℝ) ≤ (-18 * x - 1764) * g ^ 11 := by
    have g0 : 0 ≤ g ^ 11 := by positivity
    have g1 : g ^ 11 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc11) g0]
  have hc12 : (-148 : ℝ) ≤ -x - 84 := by linarith
  have t12 : (-148 : ℝ) ≤ (-x - 84) * g ^ 12 := by
    have g0 : 0 ≤ g ^ 12 := by positivity
    have g1 : g ^ 12 ≤ 1 := pow_le_one₀ hg0 hg1
    nlinarith [mul_nonneg (sub_nonneg.mpr hc12) g0]
  linarith

/-- The coefficient certificate on `[225/4, 64]`, from the sixteen pieces. Proved. -/
lemma coeff8_pos (g x : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ha : (225 / 4 : ℝ) ≤ x) (hb : x ≤ (64 : ℝ)) :
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
  rcases le_total x (3631 / 64 : ℝ) with h0 | h0
  · exact coeff8_pos_0 g x hg0 hg1 ha h0
  rcases le_total x (1831 / 32 : ℝ) with h1 | h1
  · exact coeff8_pos_1 g x hg0 hg1 h0 h1
  rcases le_total x (3693 / 64 : ℝ) with h2 | h2
  · exact coeff8_pos_2 g x hg0 hg1 h1 h2
  rcases le_total x (931 / 16 : ℝ) with h3 | h3
  · exact coeff8_pos_3 g x hg0 hg1 h2 h3
  rcases le_total x (3755 / 64 : ℝ) with h4 | h4
  · exact coeff8_pos_4 g x hg0 hg1 h3 h4
  rcases le_total x (1893 / 32 : ℝ) with h5 | h5
  · exact coeff8_pos_5 g x hg0 hg1 h4 h5
  rcases le_total x (3817 / 64 : ℝ) with h6 | h6
  · exact coeff8_pos_6 g x hg0 hg1 h5 h6
  rcases le_total x (481 / 8 : ℝ) with h7 | h7
  · exact coeff8_pos_7 g x hg0 hg1 h6 h7
  rcases le_total x (3879 / 64 : ℝ) with h8 | h8
  · exact coeff8_pos_8 g x hg0 hg1 h7 h8
  rcases le_total x (1955 / 32 : ℝ) with h9 | h9
  · exact coeff8_pos_9 g x hg0 hg1 h8 h9
  rcases le_total x (3941 / 64 : ℝ) with h10 | h10
  · exact coeff8_pos_10 g x hg0 hg1 h9 h10
  rcases le_total x (993 / 16 : ℝ) with h11 | h11
  · exact coeff8_pos_11 g x hg0 hg1 h10 h11
  rcases le_total x (4003 / 64 : ℝ) with h12 | h12
  · exact coeff8_pos_12 g x hg0 hg1 h11 h12
  rcases le_total x (2017 / 32 : ℝ) with h13 | h13
  · exact coeff8_pos_13 g x hg0 hg1 h12 h13
  rcases le_total x (4065 / 64 : ℝ) with h14 | h14
  · exact coeff8_pos_14 g x hg0 hg1 h13 h14
  exact coeff8_pos_15 g x hg0 hg1 h14 hb


set_option maxHeartbeats 4000000 in
/-- The box polynomial of the three term formula: `|P₃|² (σ+5)²` beats
`|s-1|² |s|² ⋯ |s+5|²` on `[0,1] × [15/2, 8]`, written with `Re P₃` and `Im P₃`. Proved. -/
lemma box8_poly_pos (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht0 : 15 / 2 ≤ t) (ht1 : t ≤ 8) :
    ((σ - 1) ^ 2 + t ^ 2) * (σ ^ 2 + t ^ 2) * ((σ + 1) ^ 2 + t ^ 2) * ((σ + 2) ^ 2 + t ^ 2) *
        ((σ + 3) ^ 2 + t ^ 2) * ((σ + 4) ^ 2 + t ^ 2) * ((σ + 5) ^ 2 + t ^ 2) <
      ((σ ^ 6 + 9 * σ ^ 5 - 15 * σ ^ 4 * t ^ 2 - 17 * σ ^ 4 - 90 * σ ^ 3 * t ^ 2 - 69 * σ ^ 3 + 15 * σ ^ 2 * t ^ 4 + 102 * σ ^ 2 * t ^ 2 + 2536 * σ ^ 2 + 45 * σ * t ^ 4 + 207 * σ * t ^ 2 + 12660 * σ - t ^ 6 - 17 * t ^ 4 - 2536 * t ^ 2 + 15120) ^ 2 +
          (t * (6 * σ ^ 5 + 45 * σ ^ 4 - 20 * σ ^ 3 * t ^ 2 - 68 * σ ^ 3 - 90 * σ ^ 2 * t ^ 2 - 207 * σ ^ 2 + 6 * σ * t ^ 4 + 68 * σ * t ^ 2 + 5072 * σ + 9 * t ^ 4 + 69 * t ^ 2 + 12660)) ^ 2) *
        (σ + 5) ^ 2 := by
  have hx0 : 225 / 4 ≤ t ^ 2 := by nlinarith
  have hx1 : t ^ 2 ≤ 64 := by nlinarith
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
    exact coeff8_pos σ (t ^ 2) h0 h1 hx0 hx1
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
`15/2 < Im s ≤ 8`. -/
lemma zeta_box_seven_half_eight_ineq (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (ht0 : 15 / 2 < s.im)
    (ht1 : s.im ≤ 8) :
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
  exact box8_poly_pos s.re s.im h0.le h1.le ht0.le ht1

/-- PROVED: `ζ` has no zero with `0 < Re ρ < 1` and `15/2 < Im ρ ≤ 8`, from the third order
formula `riemannZeta_eq_EM6`, the remainder bound `‖∫‖ ≤ 1/(15120(Re ρ + 5))` and the box
inequality `zeta_box_seven_half_eight_ineq`. -/
theorem riemannZeta_ne_zero_seven_half_eight (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht0 : 15 / 2 < ρ.im) (ht1 : ρ.im ≤ 8) : riemannZeta ρ ≠ 0 := by
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
  have hlt := zeta_box_seven_half_eight_ineq ρ h0 h1 ht0 ht1
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
first zero tables of `ζ`, Gram 1903 and Backlund 1914, read on the window `(8, 21/2]`: no zero
of `ζ` in the open strip has ordinate in `(8, 21/2]`. Class MEDIUM: the phase free route of the
`Feed1122ZetaSplitTen` header, Euler Maclaurin from `n = 2` with six Bernoulli terms and a
polynomial box certificate, S137 grid numerics. -/
theorem zeta_zero_free_eight_ten_half (ρ : ℂ) (h0 : riemannZeta ρ = 0) (hre0 : 0 < ρ.re)
    (hre1 : ρ.re < 1) (him : 8 < ρ.im) : 21 / 2 < ρ.im := by
  sorry

/-- `Feed1122ZetaSplitTen.zeta_zero_free_seven_half_ten_half`, exactly its statement, from the
proved range `(15/2, 8]` and the MEDIUM leaf on `(8, 21/2]`. -/
theorem zeta_zero_free_seven_half_ten_half_s137 (ρ : ℂ) (h0 : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) (him : 15 / 2 < ρ.im) : 21 / 2 < ρ.im := by
  by_cases h8 : ρ.im ≤ 8
  · exact absurd h0 (riemannZeta_ne_zero_seven_half_eight ρ hre0 hre1 him h8)
  · exact zeta_zero_free_eight_ten_half ρ h0 hre0 hre1 (not_le.mp h8)

end LeanLab.HelfgottMajor.Feed1122ZetaEight

import LeanLab.RieselVaughan1983.Lemma1Bands
import LeanLab.RieselVaughan1983.EulerGammaSharp

/-!
# P0032 Lemma 1 on `0 < x ≤ e^{-5.25}`, and so on all of `0 < x < 2`

Session PC 20261021T0003Z-5661, unit U-1299, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.

For `0 < x < 1`, with `u = −log x`, Lemma 1 asks `½u² − 2γ₀u + γ₀² − 2γ₁ < 1.641 e^{u/3}`.
Each band `[u₀, u₁]`, or `[u₀, ∞)`, uses `0.57721 < γ₀` from `EulerGammaSharp`,
`e^{u/3} ≥ E₀ (1 + h + h²/2)` with `h = (u − u₀)/3 ≥ 0` and a rational `E₀ ≤ e^{u₀/3}` from
twenty Taylor terms, and closes a quadratic inequality in `u` by `nlinarith`.

Two conditionality labels, both on the Stieltjes constant `γ₁ ≈ −0.0728158`, a parameter:
* `−0.08 < γ₁ < −0.07`, cloud51's range: `lemma1_deep_wide` on `−7.05 ≤ log x ≤ −5.25` and
  `lemma1_far_wide` on `log x ≤ −7.4`. This range cannot give `−7.368 < log x < −7.058`: there
  with `γ₁ = −0.08` and the true `γ₀` the inequality fails, worst `−0.0124` at `log x = −7.216`,
  checked in Python with mpmath.
* `−0.0729 < γ₁ < −0.07`, a sharper CITED range: `lemma1_deep` on all of `log x ≤ −5.25`, and
  `lemma1_lt_two`, Lemma 1 on `0 < x < 2`.
-/

namespace LeanLab.RieselVaughan1983

open Real Finset

/-- One band of `u = −log x ≥ u₀`, with the quadratic inequality `hq` left to the caller. -/
theorem lemma1_qband (g1 K u0 E0 : ℝ) (hK : -2 * g1 ≤ K) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h2 : Real.log x ≤ -u0) (hu0 : 2 ≤ u0) (hE : E0 ≤ Real.exp (u0 / 3))
    (hE0 : 0 ≤ E0)
    (hq : (1 / 2) * (-Real.log x) ^ 2 - 2 * (57721 / 100000) * (-Real.log x)
        + (57721 / 100000) ^ 2 + K
        < 1641 / 1000 * (E0 * (1 + (-Real.log x - u0) / 3 + ((-Real.log x - u0) / 3) ^ 2 / 2))) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hγ1 := gamma_gt_sharp
  have hγ2 := gamma_lt
  have hx1 : x < 1 := by
    rw [← Real.exp_log h0]
    calc Real.exp (Real.log x) ≤ Real.exp (-u0) := Real.exp_le_exp.mpr h2
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
  set u := -Real.log x with hu
  set h := (u - u0) / 3 with hh
  have hh0 : 0 ≤ h := by rw [hh]; linarith
  have hsplit : x ^ (-(1 / 3 : ℝ)) = Real.exp (u0 / 3) * Real.exp h := by
    rw [Real.rpow_def_of_pos h0, ← Real.exp_add]; congr 1; rw [hh, hu]; ring
  have hexph := Real.quadratic_le_exp_of_nonneg hh0
  have hP : 0 ≤ 1 + h + h ^ 2 / 2 := by positivity
  have hge : E0 * (1 + h + h ^ 2 / 2) ≤ x ^ (-(1 / 3 : ℝ)) := by
    rw [hsplit]; exact mul_le_mul hE hexph hP (Real.exp_pos _).le
  have hone : 1 ≤ x ^ (-(1 / 3 : ℝ)) := by
    rw [hsplit]
    have := Real.one_le_exp (show 0 ≤ u0 / 3 by linarith)
    have := Real.one_le_exp hh0
    nlinarith
  unfold lem1E
  rw [hfl]
  simp only [Icc_eq_empty_of_lt, zero_lt_one, sum_empty]
  have ht : Real.log x = -u := by rw [hu]; ring
  rw [ht]
  set γ := eulerMascheroniConstant
  have hmono : (1 / 2) * u ^ 2 - 2 * γ * u + γ ^ 2 ≤
      (1 / 2) * u ^ 2 - 2 * (57721 / 100000) * u + (57721 / 100000) ^ 2 := by
    have : (γ - 57721 / 100000) * (γ + 57721 / 100000 - 2 * u) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith
  rw [abs_lt]; constructor
  · nlinarith
  · nlinarith [sq_nonneg (u - 2 * γ)]

/-- `E₀ ≤ e^r` from twenty Taylor terms. -/
lemma exp_ge_of_taylor (r E0 : ℝ) (hr : 0 ≤ r)
    (h : E0 ≤ ∑ i ∈ range 20, r ^ i / (i.factorial : ℝ)) : E0 ≤ Real.exp r :=
  h.trans (Real.sum_le_exp_of_nonneg hr 20)

lemma exp_7_4 : (575460267 / 100000000 : ℝ) ≤ Real.exp ((21 / 4) / 3) :=
  exp_ge_of_taylor _ _ (by norm_num) (by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)

lemma exp_131_60 : (887584314 / 100000000 : ℝ) ≤ Real.exp ((131 / 20) / 3) :=
  exp_ge_of_taylor _ _ (by norm_num) (by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)

lemma exp_7_3 : (1031225850 / 100000000 : ℝ) ≤ Real.exp (7 / 3) :=
  exp_ge_of_taylor _ _ (by norm_num) (by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)

lemma exp_37_15 : (1178310430 / 100000000 : ℝ) ≤ Real.exp ((37 / 5) / 3) :=
  exp_ge_of_taylor _ _ (by norm_num) (by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)

lemma exp_11_5 : (902501349 / 100000000 : ℝ) ≤ Real.exp ((33 / 5) / 3) :=
  exp_ge_of_taylor _ _ (by norm_num) (by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)

lemma exp_47_20 : (1048556972 / 100000000 : ℝ) ≤ Real.exp ((141 / 20) / 3) :=
  exp_ge_of_taylor _ _ (by norm_num) (by
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


/-- Quadratic form of a band, `Q K u₀ E₀ u > 0` is the inequality `hq` of `lemma1_qband`. -/
def bandQ (K u0 E0 u : ℝ) : Prop :=
  (1 / 2) * u ^ 2 - 2 * (57721 / 100000) * u + (57721 / 100000) ^ 2 + K
    < 1641 / 1000 * (E0 * (1 + (u - u0) / 3 + ((u - u0) / 3) ^ 2 / 2))

theorem lemma1_band_of (g1 K u0 u1 E0 : ℝ) (hK : -2 * g1 ≤ K) (hg1' : g1 < -7 / 100)
    (hu0 : 2 ≤ u0) (hE : E0 ≤ Real.exp (u0 / 3)) (hE0 : 0 ≤ E0)
    (hq : ∀ u, u0 ≤ u → u ≤ u1 → bandQ K u0 E0 u) (x : ℝ) (h0 : 0 < x)
    (h1 : -u1 ≤ Real.log x) (h2 : Real.log x ≤ -u0) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) :=
  lemma1_qband g1 K u0 E0 hK hg1' x h0 h2 hu0 hE hE0 (hq _ (by linarith) (by linarith))

theorem lemma1_band_inf (g1 K u0 E0 : ℝ) (hK : -2 * g1 ≤ K) (hg1' : g1 < -7 / 100)
    (hu0 : 2 ≤ u0) (hE : E0 ≤ Real.exp (u0 / 3)) (hE0 : 0 ≤ E0)
    (hq : ∀ u, u0 ≤ u → bandQ K u0 E0 u) (x : ℝ) (h0 : 0 < x) (h2 : Real.log x ≤ -u0) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) :=
  lemma1_qband g1 K u0 E0 hK hg1' x h0 h2 hu0 hE hE0 (hq _ (by linarith))

/-! Wide range `−0.08 < γ₁`, `K = 0.16`. -/

lemma qW1 : ∀ u, 21 / 4 ≤ u → u ≤ 131 / 20 →
    bandQ (16 / 100) (21 / 4) (575460267 / 100000000) u := by
  intro u ha hb; unfold bandQ; nlinarith [sq_nonneg (u - 131 / 20)]

lemma qW2 : ∀ u, 131 / 20 ≤ u → u ≤ 7 →
    bandQ (16 / 100) (131 / 20) (887584314 / 100000000) u := by
  intro u ha hb; unfold bandQ; nlinarith [sq_nonneg (u - 7)]

lemma qW3 : ∀ u, 7 ≤ u → u ≤ 141 / 20 →
    bandQ (16 / 100) 7 (1031225850 / 100000000) u := by
  intro u ha hb; unfold bandQ; nlinarith [sq_nonneg (u - 141 / 20)]

lemma qWinf : ∀ u, 37 / 5 ≤ u → bandQ (16 / 100) (37 / 5) (1178310430 / 100000000) u := by
  intro u ha; unfold bandQ; nlinarith [sq_nonneg (u - 37 / 5)]

/-- Lemma 1 on `e^{-7.05} ≤ x ≤ e^{-5.25}`, CONDITIONAL ON `−0.08 < γ₁ < −0.07`. -/
theorem lemma1_deep_wide (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h1 : -141 / 20 ≤ Real.log x) (h2 : Real.log x ≤ -21 / 4) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hK : -2 * g1 ≤ 16 / 100 := by linarith
  rcases le_total (Real.log x) (-131 / 20) with h | h
  · rcases le_total (Real.log x) (-7) with h' | h'
    · exact lemma1_band_of g1 _ 7 (141 / 20) _ hK hg1' (by norm_num) exp_7_3 (by norm_num)
        qW3 x h0 (by linarith) (by linarith)
    · exact lemma1_band_of g1 _ (131 / 20) 7 _ hK hg1' (by norm_num) exp_131_60 (by norm_num)
        qW2 x h0 (by linarith) (by linarith)
  · exact lemma1_band_of g1 _ (21 / 4) (131 / 20) _ hK hg1' (by norm_num) exp_7_4 (by norm_num)
      qW1 x h0 (by linarith) (by linarith)

/-- Lemma 1 on `0 < x ≤ e^{-7.4}`, CONDITIONAL ON `−0.08 < γ₁ < −0.07`. -/
theorem lemma1_far_wide (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h2 : Real.log x ≤ -37 / 5) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) :=
  lemma1_band_inf g1 _ (37 / 5) _ (by linarith) hg1' (by norm_num) exp_37_15 (by norm_num)
    qWinf x h0 (by linarith)

/-! Sharper range `−0.0729 < γ₁`, `K = 0.1458`. -/

lemma qT1 : ∀ u, 21 / 4 ≤ u → u ≤ 33 / 5 →
    bandQ (1458 / 10000) (21 / 4) (575460267 / 100000000) u := by
  intro u ha hb; unfold bandQ; nlinarith [sq_nonneg (u - 33 / 5)]

lemma qT2 : ∀ u, 33 / 5 ≤ u → u ≤ 141 / 20 →
    bandQ (1458 / 10000) (33 / 5) (902501349 / 100000000) u := by
  intro u ha hb; unfold bandQ; nlinarith [sq_nonneg (u - 141 / 20)]

lemma qTinf : ∀ u, 141 / 20 ≤ u →
    bandQ (1458 / 10000) (141 / 20) (1048556972 / 100000000) u := by
  intro u ha; unfold bandQ; nlinarith [sq_nonneg (u - 9882973439601 / 1367803318420), sq_nonneg (u - 141 / 20)]

/-- Lemma 1 on `0 < x ≤ e^{-5.25}`, CONDITIONAL ON `−0.0729 < γ₁ < −0.07`. -/
theorem lemma1_deep (g1 : ℝ) (hg1 : -729 / 10000 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h2 : Real.log x ≤ -21 / 4) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hK : -2 * g1 ≤ 1458 / 10000 := by linarith
  rcases le_total (Real.log x) (-33 / 5) with h | h
  · rcases le_total (Real.log x) (-141 / 20) with h' | h'
    · exact lemma1_band_inf g1 _ (141 / 20) _ hK hg1' (by norm_num) exp_47_20 (by norm_num)
        qTinf x h0 (by linarith)
    · exact lemma1_band_of g1 _ (33 / 5) (141 / 20) _ hK hg1' (by norm_num) exp_11_5
        (by norm_num) qT2 x h0 (by linarith) (by linarith)
  · exact lemma1_band_of g1 _ (21 / 4) (33 / 5) _ hK hg1' (by norm_num) exp_7_4 (by norm_num)
      qT1 x h0 (by linarith) (by linarith)

/-- P0032 Lemma 1 on `0 < x < 2`, CONDITIONAL ON `−0.0729 < γ₁ < −0.07`, assembling
cloud51's `lemma1_case12`, `lemma1_case_e1`, `_e3`, `_e4`, `_e5` with `lemma1_deep`. -/
theorem lemma1_lt_two (g1 : ℝ) (hg1 : -729 / 10000 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h2 : x < 2) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hw : -8 / 100 < g1 := by linarith
  rcases le_or_gt 1 x with hx | hx
  · exact lemma1_case12 g1 hw hg1' x hx h2
  rcases le_total (-1) (Real.log x) with h | h
  · exact lemma1_case_e1 g1 hw hg1' x h0 h hx
  rcases le_total (-3) (Real.log x) with h' | h'
  · exact lemma1_case_e3 g1 hw hg1' x h0 h' h
  rcases le_total (-4) (Real.log x) with h'' | h''
  · exact lemma1_case_e4 g1 hw hg1' x h0 h'' h'
  rcases le_total (-21 / 4) (Real.log x) with h3 | h3
  · exact lemma1_case_e5 g1 hw hg1' x h0 h3 h''
  · exact lemma1_deep g1 hg1 hg1' x h0 h3

/-- Lemma 1 on `0 < x < 2` outside the window `−7.4 < log x < −7.05`, CONDITIONAL ON cloud51's
range `−0.08 < γ₁ < −0.07`; inside the window that range does not suffice, see the header. -/
theorem lemma1_lt_two_wide (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h2 : x < 2) (hw : Real.log x ≤ -37 / 5 ∨ -141 / 20 ≤ Real.log x) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  rcases le_or_gt 1 x with hx | hx
  · exact lemma1_case12 g1 hg1 hg1' x hx h2
  rcases le_total (-1) (Real.log x) with h | h
  · exact lemma1_case_e1 g1 hg1 hg1' x h0 h hx
  rcases le_total (-3) (Real.log x) with h' | h'
  · exact lemma1_case_e3 g1 hg1 hg1' x h0 h' h
  rcases le_total (-4) (Real.log x) with h'' | h''
  · exact lemma1_case_e4 g1 hg1 hg1' x h0 h'' h'
  rcases le_total (-21 / 4) (Real.log x) with h3 | h3
  · exact lemma1_case_e5 g1 hg1 hg1' x h0 h3 h''
  rcases hw with hw | hw
  · exact lemma1_far_wide g1 hg1 hg1' x h0 hw
  · exact lemma1_deep_wide g1 hg1 hg1' x h0 hw h3

end LeanLab.RieselVaughan1983

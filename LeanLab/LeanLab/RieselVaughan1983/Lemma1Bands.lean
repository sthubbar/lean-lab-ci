import LeanLab.RieselVaughan1983.Lemma1Div
import LeanLab.RieselVaughan1983.EulerGammaBounds

/-!
# P0032 Lemma 1 on `e^{-5.25} ≤ x ≤ e^{-4}`, by bands of width 1/4

Session 20261020T2113Z-cloud51, unit U-6740, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.
CONDITIONAL ON the numerical range `−0.08 < γ₁ < −0.07`, with `0.5693 < γ₀ < 0.5851` proved.
-/

namespace LeanLab.RieselVaughan1983

open Real Finset

lemma exp_lower (y : ℝ) (hy : 0 ≤ y) :
    27182818283 / 10000000000 * (1 + y + y ^ 2 / 2) ≤ Real.exp (1 + y) := by
  rw [Real.exp_add]
  have he := Real.exp_one_gt_d9
  have hq := Real.quadratic_le_exp_of_nonneg hy
  have : 0 ≤ 1 + y + y ^ 2 / 2 := by positivity
  nlinarith

theorem lemma1_band (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (a b lo x : ℝ)
    (h0 : 0 < x) (h1 : a ≤ Real.log x) (h2 : Real.log x ≤ b) (hb : b ≤ -3)
    (hlo : lo ≤ Real.exp (-b / 3))
    (hc : (1 / 2) * (a + 2 * (5693 / 10000)) ^ 2 - ((5693 / 10000) ^ 2 - 16 / 100) < 1641 / 1000 * lo)
    (ha : a + 2 * (5851 / 10000) ≤ 0) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  have hγ1 := gamma_gt
  have hγ2 := gamma_lt
  have hx1 : x < 1 := by
    have := Real.exp_log h0
    rw [← this]; calc Real.exp (Real.log x) ≤ Real.exp b := Real.exp_le_exp.mpr h2
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hfl : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
  have hge : lo ≤ x ^ (-(1 / 3 : ℝ)) := by
    rw [Real.rpow_def_of_pos h0]
    exact hlo.trans (Real.exp_le_exp.mpr (by linarith))
  have hlo1 : 1 ≤ Real.exp (-b / 3) := Real.one_le_exp (by linarith)
  unfold lem1E
  rw [hfl]
  simp only [Icc_eq_empty_of_lt, zero_lt_one, sum_empty]
  set t := Real.log x
  set γ := eulerMascheroniConstant
  have hneg : t + 2 * γ ≤ 0 := by linarith
  have hu : (t + 2 * γ) ^ 2 ≤ (a + 2 * (5693 / 10000)) ^ 2 := by nlinarith
  have hu0 : 0 ≤ (t + 2 * γ) ^ 2 := sq_nonneg _
  have hlo' : 1641 / 1000 * lo ≤ 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by linarith
  rw [abs_lt]; constructor <;> nlinarith

private lemma lo_of (b y : ℝ) (hy : 0 ≤ y) (hby : -b / 3 = 1 + y) :
    27182818283 / 10000000000 * (1 + y + y ^ 2 / 2) ≤ Real.exp (-b / 3) := by
  rw [hby]; exact exp_lower y hy

theorem lemma1_case_e5 (g1 : ℝ) (hg1 : -8 / 100 < g1) (hg1' : g1 < -7 / 100) (x : ℝ)
    (h0 : 0 < x) (h1 : -21 / 4 ≤ Real.log x) (h2 : Real.log x ≤ -4) :
    |lem1E g1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  rcases le_total (Real.log x) (-17 / 4) with h | h
  · rcases le_total (Real.log x) (-9 / 2) with h' | h'
    · rcases le_total (Real.log x) (-19 / 4) with h'' | h''
      · rcases le_total (Real.log x) (-5) with h3 | h3
        · exact lemma1_band g1 hg1 hg1' (-21 / 4) (-5) _ x h0 h1 h3 (by norm_num)
            (lo_of (-5) (2 / 3) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
        · exact lemma1_band g1 hg1 hg1' (-5) (-19 / 4) _ x h0 h3 h'' (by norm_num)
            (lo_of (-19 / 4) (7 / 12) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
      · exact lemma1_band g1 hg1 hg1' (-19 / 4) (-9 / 2) _ x h0 h'' h' (by norm_num)
          (lo_of (-9 / 2) (1 / 2) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
    · exact lemma1_band g1 hg1 hg1' (-9 / 2) (-17 / 4) _ x h0 h' h (by norm_num)
        (lo_of (-17 / 4) (5 / 12) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  · exact lemma1_band g1 hg1 hg1' (-17 / 4) (-4) _ x h0 h h2 (by norm_num)
      (lo_of (-4) (1 / 3) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

end LeanLab.RieselVaughan1983

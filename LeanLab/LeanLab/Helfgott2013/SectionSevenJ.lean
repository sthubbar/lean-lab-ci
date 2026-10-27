/-
P0001 H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, Section 7.2,
page 60 (PDF of v1, page 61). VERIFY unit U-1425, run 20261021T1303Z-13145.

Q-1418: the sentence after the 1.7815e-6 display says it uses `A_{η+} ≤ 8.8013` "obtained in
(7.8)", but (7.8) prints `≤ 8.7806 x` and the display multiplies by 8.7806. This file shows the
discrepancy does not reach the final (7.24) bound: even with the weaker `A_{η+} ≤ 8.8013`, the
second line of (3.36) is `≤ 1.7833 · 10⁻⁶/κ`, the sum is `≤ 3.8615 · 10⁻⁵/κ`, and the major arc
error is still `≤ 7.881 · 10⁻⁷ x²`. Only the intermediate printed constants 1.7815e-6 and
3.8613e-5 would need raising. CONDITIONAL in the same way as `eq_724_assembled`.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Helfgott2013.SectionSevenI

namespace LeanLab.Helfgott2013
open Real

/-- Second line of (3.36) with the sentence's `A_{η+} ≤ 8.8013`: at most `1.7833 · 10⁻⁶/κ`.
True value at the endpoints 1.783180e-6/κ. CONDITIONAL ON (7.2), (7.3), (7.16) and A ≤ 8.8013. -/
theorem const_17815_robust {Es A Ep np ns : ℝ} (hEs0 : 0 ≤ Es) (hEs : Es ≤ 1.9075e-8 / κ)
    (hA0 : 0 ≤ A) (hA : A ≤ 8.8013) (hEp : Ep ≤ 2.3921e-8)
    (hnp0 : 0 ≤ np) (hnp : np ≤ 0.80014) (hns0 : 0 ≤ ns) (hns : ns ^ 2 ≤ 1.77082 / κ) :
    Es * A + Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) * ns ≤ (1.7833e-6 : ℝ) / κ := by
  unfold κ at *
  have hsA : Real.sqrt A ≤ 2.96671 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hsA0 := Real.sqrt_nonneg A
  have hns' : ns ≤ 0.1901033 := by
    by_contra hc; push_neg at hc
    have : (0.1901033 : ℝ) ^ 2 < ns ^ 2 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    have : (1.77082 : ℝ) / 49 < 0.1901033 ^ 2 := by norm_num
    linarith
  have t1 : Es * A ≤ 1.9075e-8 / 49 * 8.8013 := mul_le_mul hEs hA hA0 (by norm_num)
  have t2 : Real.sqrt A + 1.6812 * np ≤ 2.96671 + 1.6812 * 0.80014 := by linarith
  have t3 : Ep * 1.6812 ≤ 2.3921e-8 * 1.6812 := by linarith
  have t4 : Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) ≤
      2.3921e-8 * 1.6812 * (2.96671 + 1.6812 * 0.80014) :=
    mul_le_mul t3 t2 (by positivity) (by norm_num)
  have t5 : Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) * ns ≤
      2.3921e-8 * 1.6812 * (2.96671 + 1.6812 * 0.80014) * 0.1901033 :=
    mul_le_mul t4 hns' hns0 (by norm_num)
  have : (1.9075e-8 : ℝ) / 49 * 8.8013 +
      2.3921e-8 * 1.6812 * (2.96671 + 1.6812 * 0.80014) * 0.1901033 ≤ 1.7833e-6 / 49 := by
    norm_num
  linarith

/-- (7.24) sum with 1.7833e-6 in place of 1.7815e-6: at most `3.8615 · 10⁻⁵`. Value 3.86145e-5. -/
theorem major_err_robust {x : ℝ} (hx : 4.9e26 ≤ x) :
    2.9387e-5 * Real.sqrt (π / 2) + 1.7833e-6 + κ * 43 * Real.log x ^ 2 / x ≤ (3.8615e-5 : ℝ) := by
  have h := major_err hx
  linarith

/-- `3.8615 · 10⁻⁵/κ ≤ 7.881 · 10⁻⁷`: the final constant of (7.24) survives. Value 7.88061e-7. -/
theorem major_err_div_robust : (3.8615e-5 : ℝ) / κ ≤ 7.881e-7 := by unfold κ; norm_num

/-- (7.24) assembled as in `eq_724_assembled`, but with the weaker hypothesis `A ≤ 8.8013` of
the page 60 sentence. CONDITIONAL ON the same inputs. The conclusion `≤ 7.881 · 10⁻⁷ x²` is
unchanged, so Q-1418 has no effect on (7.24), (7.25) or Section 7.4. -/
theorem eq_724_robust {x e ε d3 Es A Ep np ns Zp Zs LSs LSp : ℝ} (hx : 4.9e26 ≤ x)
    (he0 : 0 ≤ e) (he : e ≤ 0.8001288) (hε0 : 0 ≤ ε) (h75 : ε * e ≤ 2.42942e-6)
    (hd0 : 0 ≤ d3) (hd : d3 ≤ 32.5023)
    (hEs0 : 0 ≤ Es) (hEs : Es ≤ 1.9075e-8 / κ) (hA0 : 0 ≤ A) (hA : A ≤ 8.8013)
    (hEp : Ep ≤ 2.3921e-8) (hnp0 : 0 ≤ np) (hnp : np ≤ 0.80014)
    (hns0 : 0 ≤ ns) (hns : ns ^ 2 ≤ 1.77082 / κ)
    (hZp0 : 0 ≤ Zp) (hZp : Zp ≤ 0.640209 * Real.log x) (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * Real.log x)
    (hLSs0 : 0 ≤ LSs) (hLSs : LSs ≤ 24.32 * Real.log x + 0.57)
    (hLSp0 : 0 ≤ LSp) (hLSp : LSp ≤ 18.57 * Real.log x + 28.39) :
    (2.82643 * e ^ 2 * (2 + ε) * ε + (4.31004 * e ^ 2 + 0.0012 * d3 ^ 2 / 8 ^ 5) / 150000) *
          (Real.sqrt (π / 2) / κ) * x ^ 2 +
        (Es * A + Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) * ns) * x ^ 2 +
        (2 * Zp * LSs + 4 * Real.sqrt (Zp * Zs) * LSp) * x ≤ 7.881e-7 * x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hk : (0 : ℝ) < κ := by unfold κ; norm_num
  have h1 := const_29387 he0 he hε0 h75 hd0 hd
  have h2 := const_17815_robust hEs0 hEs hA0 hA hEp hnp0 hnp hns0 hns
  have h3 := third_line_43 (log_x_ge hx) hZp0 hZp hZs0 hZs hLSs0 hLSs hLSp0 hLSp
  have hm := major_err_robust hx
  have hdv := major_err_div_robust
  have hs0 : 0 ≤ Real.sqrt (π / 2) / κ * x ^ 2 := by positivity
  have b1 : (2.82643 * e ^ 2 * (2 + ε) * ε + (4.31004 * e ^ 2 + 0.0012 * d3 ^ 2 / 8 ^ 5) / 150000) *
      (Real.sqrt (π / 2) / κ) * x ^ 2 ≤ 2.9387e-5 * (Real.sqrt (π / 2) / κ * x ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hs0
  have b2 : (Es * A + Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) * ns) * x ^ 2 ≤
      1.7833e-6 / κ * x ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
  have b3 : (2 * Zp * LSs + 4 * Real.sqrt (Zp * Zs) * LSp) * x ≤ 43 * Real.log x ^ 2 * x :=
    mul_le_mul_of_nonneg_right h3 hx0.le
  have key : 2.9387e-5 * (Real.sqrt (π / 2) / κ * x ^ 2) + 1.7833e-6 / κ * x ^ 2 +
      43 * Real.log x ^ 2 * x =
      (2.9387e-5 * Real.sqrt (π / 2) + 1.7833e-6 + κ * 43 * Real.log x ^ 2 / x) * (x ^ 2 / κ) := by
    field_simp
  have b4 : (2.9387e-5 * Real.sqrt (π / 2) + 1.7833e-6 + κ * 43 * Real.log x ^ 2 / x) * (x ^ 2 / κ) ≤
      3.8615e-5 * (x ^ 2 / κ) := mul_le_mul_of_nonneg_right hm (by positivity)
  have b5 : 3.8615e-5 * (x ^ 2 / κ) ≤ 7.881e-7 * x ^ 2 := by
    rw [show 3.8615e-5 * (x ^ 2 / κ) = (3.8615e-5 / κ) * x ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hdv (by positivity)
  linarith

/-- Vacuity of `eq_724_robust` at the boundary `A = 8.8013`, all other inputs as in `vacuity_724`. -/
theorem vacuity_724_robust :
    (2.82643 * 0.8001287 ^ 2 * (2 + 0) * 0 + (4.31004 * 0.8001287 ^ 2 + 0.0012 * 32.5023 ^ 2 / 8 ^ 5) / 150000) *
          (Real.sqrt (π / 2) / κ) * (4.9e26 : ℝ) ^ 2 +
        (0 * 8.8013 + 0 * 1.6812 * (Real.sqrt 8.8013 + 1.6812 * 0.8) * 0) * (4.9e26 : ℝ) ^ 2 +
        (2 * 0 * 0 + 4 * Real.sqrt (0 * 0) * 0) * (4.9e26 : ℝ) ≤ 7.881e-7 * (4.9e26 : ℝ) ^ 2 := by
  have hl := log_x_ge (le_refl (4.9e26 : ℝ))
  exact eq_724_robust (le_refl _) (by norm_num) (by norm_num) (le_refl _) (by norm_num)
    (by norm_num) (le_refl _) (le_refl _) (by unfold κ; norm_num) (by norm_num) (le_refl _)
    (by norm_num) (by norm_num) (by norm_num) (le_refl _) (by unfold κ; norm_num)
    (le_refl _) (by linarith) (le_refl _) (by linarith) (le_refl _) (by linarith) (le_refl _)
    (by linarith)

end LeanLab.Helfgott2013

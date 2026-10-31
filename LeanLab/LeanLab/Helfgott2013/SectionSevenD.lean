/-
P0001 Helfgott 2013, arXiv 1312.7748v2, Section 7.3, pages 64 and 65: the bounds on
`R_{z,t}` at `t = 2r₀` and `t = 2r₁`, (7.33), (7.34), (7.36) and (7.39).

(7.38) in the paper is a numerical claim: "the bisection method with 32 iterations shows
`f(t) ≤ 0.019562618` for `180 ≤ t ≤ 30000`", with separate arguments below 180 and above
30000. Python with 30 digits puts the true maximum at `t ≈ 516.18`, value `0.0195626172`, so
the printed bound holds with margin `8 · 10⁻¹⁰`, MATCH. Here a rigorous replacement is PROVED:
`f(t) ≤ 0.0196` for EVERY `t > 0`, by the tangent line of `log` at `516`, and it is enough for
the printed (7.39) `R_{y/K,2r₁} ≤ 0.71392`.
Formulas read from the rendered page images of pages 64 and 65.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is Helfgott's theorem.
-/
import Mathlib
import LeanLab.Helfgott2013.SectionSevenC

open Real Finset

noncomputable section
namespace LeanLab.Helfgott2013.SectionSevenD

open LeanLab.ChenExplicit.Gamma LeanLab.Helfgott2013.SectionSevenC

/-! ### Small logarithms -/

theorem l1002_bounds : (0.001998 : ℝ) ≤ log 1.002 ∧ log (1.002 : ℝ) ≤ 0.0019981 := by
  constructor
  · have h := log_one_add_inv_ge (a := (500 : ℝ)) (by norm_num)
    rw [show (1 : ℝ) + (500 : ℝ)⁻¹ = 1.002 by norm_num] at h
    norm_num at h; linarith
  · have h := LeanLab.ChenExplicit.Gamma.log_one_add_inv_le_sum (a := (500 : ℝ)) (by norm_num) 1
    simp only [sum_range_succ, sum_range_zero] at h
    rw [show (1 : ℝ) + (500 : ℝ)⁻¹ = 1.002 by norm_num] at h
    norm_num at h; linarith

/-- `Λ = log(12 · 2^{1/3} / 2.004) = (7/3) log 2 + log(3/2) - log 1.002`. -/
def Λ : ℝ := log (12 * 2 ^ (1 / 3 : ℝ) / 2.004)

theorem Λ_eq : Λ = 7 / 3 * log 2 + log (3 / 2) - log 1.002 := by
  unfold Λ
  have h12 : (12 : ℝ) = 2 ^ 3 * (3 / 2) := by norm_num
  have h2004 : (2.004 : ℝ) = 2 * 1.002 := by norm_num
  rw [log_div (by positivity) (by norm_num), log_mul (by norm_num) (by positivity),
    log_rpow (by norm_num), h12, log_mul (by norm_num) (by norm_num), log_pow, h2004,
    log_mul (by norm_num) (by norm_num)]
  push_cast; ring

theorem Λ_bounds : (2.02081 : ℝ) ≤ Λ ∧ Λ ≤ 2.020812 := by
  rw [Λ_eq]
  have := log_two_gt_d9; have := log_two_lt_d9
  have := l32_lo; have := l32_hi; have := l1002_bounds
  constructor <;> nlinarith

/-- `K₂ = 2 log(12 · 2^{1/3} / 2.004)`, the constant of (7.37) and `f`. -/
def Kc : ℝ := 2 * Λ

/-- `c = 4 log(12 · 2^{1/3} / 2.004) - log 3`, page 65. -/
def cc : ℝ := 4 * Λ - log 3

theorem log3_bounds : (1.0986122883 : ℝ) < log 3 ∧ log (3 : ℝ) < 1.0986122890 := by
  have e : log (3 : ℝ) = log 2 + log (3 / 2) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  have := log_two_gt_d9; have := log_two_lt_d9; have := l32_lo; have := l32_hi
  constructor <;> linarith

/-- `f(t) = ((4/3) log t - c) / ((2/15) t - (2/3) log t + 2 log(12 · 2^{1/3}/2.004))`, page 65. -/
def f (t : ℝ) : ℝ := (4 / 3 * log t - cc) / (2 / 15 * t - 2 / 3 * log t + Kc)

/-- The denominator of `f` is at least `3.6` for every `t > 0`, by `log t ≤ log 5 + t/5 - 1`. -/
theorem den_ge {t : ℝ} (ht : 0 < t) : (3.6 : ℝ) ≤ 2 / 15 * t - 2 / 3 * log t + Kc := by
  have h := log_le_sub_one_of_pos (show 0 < t / 5 by positivity)
  rw [log_div ht.ne' (by norm_num)] at h
  have h5 : log (5 : ℝ) < 1.61 := by
    have e : log (5 : ℝ) = 2 * log 2 + log (5 / 4) := by
      rw [show (5 : ℝ) = 2 ^ 2 * (5 / 4) by norm_num, log_mul (by norm_num) (by norm_num),
        log_pow]; push_cast; ring_nf
    rw [e]; have := log_two_lt_d9; have := l54_hi; linarith
  have := Λ_bounds
  unfold Kc
  linarith

/-- **(7.38), rigorous form: `f(t) ≤ 0.0196` for every `t > 0`.** The paper's bisection gives
`0.019562618` on `[180, 30000]`; this weaker bound holds everywhere and suffices for (7.39). -/
theorem f_le {t : ℝ} (ht : 0 < t) : f t ≤ 0.0196 := by
  have hD := den_ge ht
  unfold f
  rw [div_le_iff₀ (by linarith)]
  -- tangent line of log at 516
  have h := log_le_sub_one_of_pos (show 0 < t / 516 by positivity)
  rw [log_div ht.ne' (by norm_num)] at h
  have h516 : log (516 : ℝ) ≤ 9 * 0.6931471808 + 1 / 128 := by
    have e : log (516 : ℝ) = 9 * log 2 + log (1 + 1 / 128) := by
      rw [show (516 : ℝ) = 2 ^ 9 * (1 + 1 / 128) by norm_num,
        log_mul (by norm_num) (by norm_num), log_pow]; push_cast; ring
    rw [e]
    have := log_two_lt_d9
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 128 by norm_num)
    linarith
  have hΛ := Λ_bounds
  have h3 := log3_bounds
  unfold Kc cc
  nlinarith

/-- `f(t) > -2` for `t ≥ 1`, so `3 + f(t) > 0` and the logarithm in (7.39) is the usual one. -/
theorem f_gt {t : ℝ} (ht : 1 ≤ t) : -2 < f t := by
  have hD := den_ge (by linarith : (0 : ℝ) < t)
  have hl := log_nonneg ht
  have hΛ := Λ_bounds
  have h3 := log3_bounds
  unfold f
  rw [lt_div_iff₀ (by linarith)]
  unfold cc
  nlinarith

/-- **(7.39): `R_{y/K,2r₁} = 0.27125 log(3 + f(log y)) + 0.41415 ≤ 0.71392`** for `y ≥ e`,
in the third-line form of (7.37). MATCHES; with the paper's 0.019562618 it is `0.7139116`. -/
theorem R739 {t : ℝ} (ht : 1 ≤ t) : 0.27125 * log (3 + f t) + 0.41415 ≤ (0.71392 : ℝ) := by
  have h1 := f_le (by linarith : (0 : ℝ) < t)
  have h2 := f_gt ht
  have hmono : log (3 + f t) ≤ log (3.0196 : ℝ) := log_le_log (by linarith) (by linarith)
  have e : log (3.0196 : ℝ) = log 3 + log (1 + (3 / 0.0196 : ℝ)⁻¹) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have hs := LeanLab.ChenExplicit.Gamma.log_one_add_inv_le_sum (a := (3 / 0.0196 : ℝ))
    (by norm_num) 1
  simp only [sum_range_succ, sum_range_zero] at hs
  norm_num at hs
  have h3 := log3_bounds
  rw [e] at hmono
  norm_num at hmono
  nlinarith

/-- (7.37), second line to third line: `1 + N/D = 3 + f(t)` with `N = (4/15) t + log 3` and
`D = (2/15) t - (2/3) log t + 2 log(12 · 2^{1/3}/2.004)`, for `t > 0`. MATCHES. -/
theorem eq737 {t : ℝ} (ht : 0 < t) :
    1 + (4 / 15 * t + log 3) / (2 / 15 * t - 2 / 3 * log t + Kc) = 3 + f t := by
  have hD := den_ge ht
  unfold f cc Kc at *
  have hne : 2 / 15 * t - 2 / 3 * log t + 2 * Λ ≠ 0 := by linarith
  set D := 2 / 15 * t - 2 / 3 * log t + 2 * Λ with hDdef
  have key : 4 / 15 * t + log 3 = (4 / 3 * log t - (4 * Λ - log 3)) + 2 * D := by
    rw [hDdef]; ring
  rw [key, add_div, mul_div_cancel_right₀ _ hne]; ring

/-! ### (7.36) -/

/-- **(7.36): `R_{y,2r₁} ≤ 0.71215` for `y ≥ 10²⁵`**, in the second-line form with `t = log y`:
the fraction is at most `2` because `log 3 ≤ 4 log(9 / (2.004 · 3/4))`. MATCHES. -/
theorem R736 {t : ℝ} (ht : 1 ≤ t) :
    0.27125 * log (1 + (4 / 15 * t + log 3) /
      (2 * (1 / 3 - 4 / 15) * t + 2 * log (9 / (2.004 * (3 / 4))))) + 0.41415 ≤ (0.71215 : ℝ) := by
  have hM : (1.78 : ℝ) ≤ log (9 / (2.004 * (3 / 4))) := by
    have e : log (9 / (2.004 * (3 / 4)) : ℝ) = 2 * log 2 + log (3 / 2) - log 1.002 := by
      rw [show (9 / (2.004 * (3 / 4)) : ℝ) = 2 ^ 2 * (3 / 2) / 1.002 by norm_num,
        log_div (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num), log_pow]
      push_cast; ring
    rw [e]; have := log_two_gt_d9; have := l32_lo; have := l1002_bounds; linarith
  have h3 := log3_bounds
  have hD : 0 < 2 * (1 / 3 - 4 / 15) * t + 2 * log (9 / (2.004 * (3 / 4))) := by nlinarith
  have hF0 : 0 ≤ (4 / 15 * t + log 3) / (2 * (1 / 3 - 4 / 15) * t +
      2 * log (9 / (2.004 * (3 / 4)))) := div_nonneg (by linarith) hD.le
  have hF : (4 / 15 * t + log 3) / (2 * (1 / 3 - 4 / 15) * t +
      2 * log (9 / (2.004 * (3 / 4)))) ≤ 2 := by
    rw [div_le_iff₀ hD]; nlinarith
  have hl : log (1 + (4 / 15 * t + log 3) / (2 * (1 / 3 - 4 / 15) * t +
      2 * log (9 / (2.004 * (3 / 4))))) ≤ log 3 :=
    log_le_log (by linarith) (by linarith)
  nlinarith

end LeanLab.Helfgott2013.SectionSevenD

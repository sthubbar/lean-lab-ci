/-
P0001 H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2,
Section 7.2 "The total major-arc contribution", PDF pages about 58 to 60, displays (7.9) to (7.25).
Read in Claude in Chrome on arxiv.org/html/1312.7748v2, unit U-1418, run 20261021T1303Z-13145.

This file checks the arithmetic of Section 7.2 that produces the constants 0.000834 of (7.13)
and 2.9387e-5, 1.7815e-6 and 43 (log x)² x of (7.24). The analytic inputs, Proposition 3.2
display (3.36), [Hela] Cor. 1.3, Prop. 1.5, § B.5, and the norm values (7.4) to (7.8), are NOT
proved here; each enters as a named hypothesis, so every theorem using one is CONDITIONAL.
The sup lemmas `phi_sup` and `phi_t_sup` and all purely numerical steps are unconditional.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Helfgott2013.SectionSevenB

namespace LeanLab.Helfgott2013
open Real

/-! ### The second integral of (7.11): the constant 2.0002 -/

/-- Mellin moments of `η₂ = η₁ *_M η₁`, `η₁ = 2 · 1_{[1/2,1]}`: `∫η₂ w² = (7/12)² = 49/144`,
`∫η₂ w = (3/4)² = 9/16`, and `3 · 49/144 = 49/48`. Rational arithmetic only. -/
theorem eta2_moments :
    (2 * (1 - (1 / 2 : ℝ) ^ 3) / 3) ^ 2 = 49 / 144 ∧ (2 * (1 - (1 / 2 : ℝ) ^ 2) / 2) ^ 2 = 9 / 16 ∧
      (3 : ℝ) * (49 / 144) = 49 / 48 := by
  norm_num

/-- Page 58: with `c₁ = (9/4)/√(2π)`,
`(49/48)√(π/2) − (9/4)c₁ + √(π/2)c₁² = (49/48)√(π/2) − (9/4)²/(2√(2π))`. -/
theorem c1_identity :
    49 / 48 * Real.sqrt (π / 2) - 9 / 4 * ((9 / 4) / Real.sqrt (2 * π)) +
        Real.sqrt (π / 2) * ((9 / 4) / Real.sqrt (2 * π)) ^ 2 =
      49 / 48 * Real.sqrt (π / 2) - (9 / 4) ^ 2 / (2 * Real.sqrt (2 * π)) := by
  have hpi := Real.pi_pos
  have hq2 : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hqs : Real.sqrt (2 * π) * Real.sqrt (π / 2) = π := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 * π * (π / 2) = π * π by ring, Real.sqrt_mul_self hpi.le]
  have hq0 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hs0 : 0 < Real.sqrt (π / 2) := Real.sqrt_pos.mpr (by positivity)
  set q := Real.sqrt (2 * π)
  set s := Real.sqrt (π / 2)
  have key : s * ((9 / 4) / q) ^ 2 = (9 / 4) ^ 2 / (2 * q) := by
    rw [div_pow, hq2, ← hqs]; field_simp
  rw [key]; field_simp; ring

/-- Page 58: `2.71 · |η◦'|₂² ≤ 7.4188` with `|η◦'|₂² = 2.7375292…` from (7.6). MATCHES, 7.418704. -/
theorem eta_prime_coef {d : ℝ} (hd : d ≤ 2.7375293) : 2.71 * d ≤ (7.4188 : ℝ) := by
  linarith

/-- Page 58: `7.4188 ((49/48)√(π/2) − (9/4)²/(2√(2π))) ≤ 2.0002`. MATCHES, value 2.0001248. -/
theorem step_20002 :
    7.4188 * (49 / 48 * Real.sqrt (π / 2) - (9 / 4) ^ 2 / (2 * Real.sqrt (2 * π))) ≤ (2.0002 : ℝ) := by
  have hs := sqrt_pi_half_lt
  have hq := sqrt_two_pi_lt
  have hq0 := sqrt_two_pi_gt
  have h : (9 / 4 : ℝ) ^ 2 / (2 * 2.50663) ≤ (9 / 4) ^ 2 / (2 * Real.sqrt (2 * π)) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have h' : (9 / 4 : ℝ) ^ 2 / (2 * 2.50663) = 5.0625 / 5.01326 := by norm_num
  rw [h'] at h
  have : (7.4188 : ℝ) * (49 / 48 * 1.25331414 - 5.0625 / 5.01326) ≤ 2.0002 := by norm_num
  nlinarith

/-! ### (7.13): the constant 0.000834 -/

/-- `exp(−4802) ≤ 6/4802³`, from `x³/3! ≤ eˣ`. Here `4802 = 2κ²`. -/
theorem exp_neg_4802 : Real.exp (-4802) ≤ 6 / 4802 ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (4802 : ℝ) (by norm_num) 3
  rw [Real.exp_neg]
  have hpos : (0 : ℝ) < 4802 ^ 3 / 6 := by norm_num
  have : (4802 : ℝ) ^ 3 / (Nat.factorial 3 : ℝ) = 4802 ^ 3 / 6 := by norm_num [Nat.factorial]
  rw [this] at h
  rw [show (6 : ℝ) / 4802 ^ 3 = (4802 ^ 3 / 6)⁻¹ by field_simp]
  exact inv_anti₀ hpos h

/-- (7.13) constant, page 58: with `κ = 49` and `|η◦|₂² ≤ 0.8001288²` from (7.4),
`κ (|η◦|₂² (2 + 1/κ²) e^{−2κ²} + 2.0002/κ³) ≤ 0.000834`. MATCHES, value 0.00083307. -/
theorem const_000834 {e2 : ℝ} (h0 : 0 ≤ e2) (h : e2 ≤ 0.8001288 ^ 2) :
    κ * (e2 * (2 + 1 / κ ^ 2) * Real.exp (-(2 * κ ^ 2)) + 2.0002 / κ ^ 3) ≤ (0.000834 : ℝ) := by
  unfold κ
  have hE := exp_neg_4802
  have hE0 := (Real.exp_pos (-4802)).le
  have e1 : -(2 * (49 : ℝ) ^ 2) = -4802 := by norm_num
  rw [e1]
  have h1 : e2 * (2 + 1 / (49 : ℝ) ^ 2) ≤ 0.8001288 ^ 2 * (2 + 1 / 49 ^ 2) :=
    mul_le_mul_of_nonneg_right h (by norm_num)
  have h2 : e2 * (2 + 1 / (49 : ℝ) ^ 2) * Real.exp (-4802) ≤
      0.8001288 ^ 2 * (2 + 1 / 49 ^ 2) * (6 / 4802 ^ 3) :=
    mul_le_mul h1 hE hE0 (by norm_num)
  have : (49 : ℝ) * (0.8001288 ^ 2 * (2 + 1 / 49 ^ 2) * (6 / 4802 ^ 3) + 2.0002 / 49 ^ 3) ≤ 0.000834 := by
    norm_num
  nlinarith

/-- (7.13), page 58, CONDITIONAL ON the display before it, which follows from (7.11), (7.12)
and the 2.0002 bound: `C ≥ (1/κ)P e₂ − e₂(2 + 1/κ²)e^{−2κ²} − 2.0002/κ³` with `P = |ϕ|₁`,
`e₂ = |η◦|₂²`. Then `C ≥ (1/κ)(P e₂ − 0.000834)`. MATCHES. -/
theorem eq_713 {C P e2 : ℝ} (h0 : 0 ≤ e2) (h : e2 ≤ 0.8001288 ^ 2)
    (hpre : (1 / κ) * P * e2 - e2 * (2 + 1 / κ ^ 2) * Real.exp (-(2 * κ ^ 2)) - 2.0002 / κ ^ 3 ≤ C) :
    (1 / κ) * (P * e2 - 0.000834) ≤ C := by
  have hc := const_000834 h0 h
  have hk : (0 : ℝ) < κ := by unfold κ; norm_num
  have : (1 / κ) * (P * e2 - 0.000834) ≤
      (1 / κ) * P * e2 - e2 * (2 + 1 / κ ^ 2) * Real.exp (-(2 * κ ^ 2)) - 2.0002 / κ ^ 3 := by
    have : (1 / κ) * (P * e2 - 0.000834) =
        (1 / κ) * P * e2 - (1 / κ) * 0.000834 := by ring
    rw [this]
    have h2 : e2 * (2 + 1 / κ ^ 2) * Real.exp (-(2 * κ ^ 2)) + 2.0002 / κ ^ 3 ≤ (1 / κ) * 0.000834 := by
      calc e2 * (2 + 1 / κ ^ 2) * Real.exp (-(2 * κ ^ 2)) + 2.0002 / κ ^ 3
          = (κ * (e2 * (2 + 1 / κ ^ 2) * Real.exp (-(2 * κ ^ 2)) + 2.0002 / κ ^ 3)) / κ := by
            field_simp
        _ ≤ 0.000834 / κ := by gcongr
        _ = (1 / κ) * 0.000834 := by ring
    linarith
  linarith

/-- Page 58: `|ϕ|₁ |η◦|₂² = 0.80237…` with `|ϕ|₁ = √(π/2)` and (7.4). MATCHES. -/
theorem phi1_eta2 {e : ℝ} (h1 : 0.8001287 ≤ e) (h2 : e ≤ 0.8001288) :
    0.80237 ≤ Real.sqrt (π / 2) * e ^ 2 ∧ Real.sqrt (π / 2) * e ^ 2 ≤ (0.80238 : ℝ) := by
  have hs := sqrt_pi_half_lt
  have hs' := sqrt_pi_half_gt
  have he1 : (0.8001287 : ℝ) ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  have he2 : e ^ 2 ≤ (0.8001288 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
  constructor <;> nlinarith

/-! ### (7.16), (7.17) and the `err_{η*,χ_T}` bound -/

theorem sqrt_xplus_ge {x : ℝ} (hx : 4.9e26 ≤ x) : (2.2135943e13 : ℝ) ≤ Real.sqrt x := by
  rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith

theorem sqrt_300000_lt : Real.sqrt 300000 < (547.7226 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- (7.16), page 59: `4.269 · 10⁻¹⁴ + (380600 + 76√300000)/√x₊ ≤ 1.9075 · 10⁻⁸` for
`x ≥ x₊ = 4.9 · 10²⁶`. MATCHES, value 1.907431e-8. The first inequality of (7.16) is [Hela, Cor. 1.3]. -/
theorem eq_716 {x : ℝ} (hx : 4.9e26 ≤ x) :
    4.269e-14 + (380600 + 76 * Real.sqrt 300000) / Real.sqrt x ≤ (1.9075e-8 : ℝ) := by
  have hq := sqrt_xplus_ge hx
  have hr := sqrt_300000_lt
  have hr0 := Real.sqrt_nonneg (300000 : ℝ)
  have h1 : (380600 + 76 * Real.sqrt 300000) / Real.sqrt x ≤ (380600 + 76 * 547.7226) / 2.2135943e13 := by
    apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) hq
  have : (4.269e-14 : ℝ) + (380600 + 76 * 547.7226) / 2.2135943e13 ≤ 1.9075e-8 := by norm_num
  linarith

/-- Page 59: `|err_{η*,χ_T}(0, x)| ≤ 4.269 · 10⁻¹⁴ + 380676/√x₊ ≤ 1.71973 · 10⁻⁸`. MATCHES,
value 1.7197231e-8. -/
theorem err_chiT {x : ℝ} (hx : 4.9e26 ≤ x) :
    4.269e-14 + (380600 + 76) / Real.sqrt x ≤ (1.71973e-8 : ℝ) := by
  have hq := sqrt_xplus_ge hx
  have h1 : (380600 + 76 : ℝ) / Real.sqrt x ≤ (380600 + 76) / 2.2135943e13 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq
  have : (4.269e-14 : ℝ) + (380600 + 76) / 2.2135943e13 ≤ 1.71973e-8 := by norm_num
  linarith

/-- (7.17), page 59: `2 · 10⁻⁶ + 310.84/√x ≤ 3 · 10⁻⁶` for `x ≥ x₊`, so the coefficient is
`0.640206 + 3 · 10⁻⁶ = 0.640209`. MATCHES. The asymptotic itself is [Hela, Prop. 1.5]. -/
theorem eq_717 {x : ℝ} (hx : 4.9e26 ≤ x) :
    2e-6 + 310.84 / Real.sqrt x ≤ (3e-6 : ℝ) ∧ (0.640206 : ℝ) + 3e-6 = 0.640209 := by
  have hq := sqrt_xplus_ge hx
  have h1 : (310.84 : ℝ) / Real.sqrt x ≤ 310.84 / 2.2135943e13 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq
  have : (2e-6 : ℝ) + 310.84 / 2.2135943e13 ≤ 3e-6 := by norm_num
  constructor
  · linarith
  · norm_num

/-! ### Sup norms: (7.19), the 0.732513 bound, `|ϕ · t|∞`, (7.22) -/

/-- `u e^{−u} ≤ e^{−1}` for every real `u`, from `1 + y ≤ e^y`. -/
theorem mul_exp_neg_le (u : ℝ) : u * Real.exp (-u) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (u - 1)
  have he : Real.exp (u - 1) * Real.exp (-u) = Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have hp := (Real.exp_pos (-u)).le
  calc u * Real.exp (-u) ≤ Real.exp (u - 1) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right (by linarith) hp
    _ = Real.exp (-1) := he

/-- `|ϕ|∞ = 2/e` for `ϕ(t) = t² e^{−t²/2}`: the bound used in (7.19), page 59. PROVED. -/
theorem phi_sup (t : ℝ) : t ^ 2 * Real.exp (-(t ^ 2 / 2)) ≤ 2 * Real.exp (-1) := by
  have h := mul_exp_neg_le (t ^ 2 / 2)
  nlinarith

/-- `|ϕ · t|∞ = 3^{3/2} e^{−3/2}`, page 59, in squared form:
`(t³ e^{−t²/2})² = t⁶ e^{−t²} ≤ 27 e^{−3}`. PROVED. -/
theorem phi_t_sup (t : ℝ) : t ^ 6 * Real.exp (-t ^ 2) ≤ 27 * Real.exp (-3) := by
  set u := t ^ 2 / 3 with hu
  have hu0 : 0 ≤ u := by positivity
  have h := mul_exp_neg_le u
  have hp : 0 ≤ u * Real.exp (-u) := mul_nonneg hu0 (Real.exp_pos _).le
  have h3 : (u * Real.exp (-u)) ^ 3 ≤ Real.exp (-1) ^ 3 := pow_le_pow_left₀ hp h 3
  have e1 : Real.exp (-1) ^ 3 = Real.exp (-3) := by
    rw [← Real.exp_nat_mul]; norm_num
  have e2 : Real.exp (-u) ^ 3 = Real.exp (-t ^ 2) := by
    rw [← Real.exp_nat_mul, hu]; ring_nf
  have e3 : t ^ 6 * Real.exp (-t ^ 2) = 27 * (u * Real.exp (-u)) ^ 3 := by
    rw [mul_pow, e2, hu]; ring
  rw [e3, ← e1]; linarith

/-- `√(27 e^{−3}) = (3/e)^{3/2} ≤ 1.15942`. True 1.1594183. -/
theorem phi_t_value : Real.sqrt (27 * Real.exp (-3)) ≤ (1.15942 : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 3 := by
    rw [e3]; exact pow_le_pow_left₀ (by norm_num) h1.le 3
  rw [Real.exp_neg]
  have h4 : (Real.exp 3)⁻¹ ≤ ((2.7182818283 : ℝ) ^ 3)⁻¹ := inv_anti₀ (by norm_num) h3
  have : (27 : ℝ) * ((2.7182818283 : ℝ) ^ 3)⁻¹ ≤ 1.15942 ^ 2 := by norm_num
  linarith

/-- Page 59: `|η₂(t)/t|₁ = 4 (log 2)² ≤ 1.921813` and `1.921813 · 0.381157 ≤ 0.732513`.
MATCHES, 1.9218121 and 0.7325125. The value 0.381157 of `|ϕ · log⁺|∞` is the paper's
bisection and is NOT checked here. -/
theorem eta2_t_norm :
    4 * Real.log 2 ^ 2 ≤ (1.921813 : ℝ) ∧ (1.921813 : ℝ) * 0.381157 ≤ 0.732513 := by
  have h1 := Real.log_two_lt_d9
  have h0 := Real.log_two_gt_d9
  constructor
  · nlinarith
  · norm_num

/-- (7.22), page 59: `1.064735 + 3.25312 (1 + (4/π) log 200)/200 ≤ 1.19073`. MATCHES,
value 1.1907288. The equality before it is [Hela, § B.5]. -/
theorem eq_722 : 1.064735 + 3.25312 * (1 + 4 / π * Real.log 200) / 200 ≤ (1.19073 : ℝ) := by
  have hp := Real.pi_gt_d6
  have hl := log_200_lt
  have hl0 : 0 ≤ Real.log 200 := Real.log_nonneg (by norm_num)
  have h1 : 4 / π ≤ 4 / 3.141592 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  have h2 : 4 / π * Real.log 200 ≤ 4 / 3.141592 * 5.298318 :=
    mul_le_mul h1 hl.le hl0 (by norm_num)
  have : (1.064735 : ℝ) + 3.25312 * (1 + 4 / 3.141592 * 5.298318) / 200 ≤ 1.19073 := by norm_num
  linarith

/-! ### (7.21) and (7.23) -/

theorem log_150000_lt : Real.log 150000 < 11.918393 := by
  have e : Real.log 150000 = Real.log 300000 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have := log_300000_lt
  have := Real.log_two_gt_d9
  rw [e]; linarith

theorem log_150000_pos : 0 ≤ Real.log 150000 := Real.log_nonneg (by norm_num)

/-- (7.21), page 59: `(√(π/2)/49 + 1.71973 · 10⁻⁸)(0.732513 + 1.414 log(x/49)) ≤ 0.0362 log x`
for every `x ≥ 49`. MATCHES, the `log x` coefficient is 0.0361671. -/
theorem eq_721 {x : ℝ} (hx : 49 ≤ x) :
    (Real.sqrt (π / 2) / 49 + 1.71973e-8) * (0.732513 + 1.414 * Real.log (x / 49)) ≤
      0.0362 * Real.log x := by
  have hs := sqrt_pi_half_lt
  have hs0 := Real.sqrt_nonneg (π / 2)
  have hl : Real.log (x / 49) = Real.log x - Real.log 49 :=
    Real.log_div (by linarith) (by norm_num)
  have h49 : Real.log 4 ≤ Real.log 49 := Real.log_le_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have hLx : Real.log 49 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  set a := Real.sqrt (π / 2) / 49 + 1.71973e-8 with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a * 1.414 ≤ 0.0362 := by rw [ha]; nlinarith
  have hL0 : 0 ≤ Real.log x := by linarith
  have e : a * (0.732513 + 1.414 * Real.log (x / 49)) =
      (a * 1.414) * Real.log x + a * (0.732513 - 1.414 * Real.log 49) := by rw [hl]; ring
  have t1 : (a * 1.414) * Real.log x ≤ 0.0362 * Real.log x := mul_le_mul_of_nonneg_right ha1 hL0
  have t2 : a * (0.732513 - 1.414 * Real.log 49) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha0 (by linarith)
  rw [e]; linarith

/-- (7.23), page 59, for `η*`: `(1.414/log 2 · L + 2 S/49) log r ≤ 24.32 L + 0.57` for `L ≥ 0`,
`r = 150000` and `S = (3/e)^{3/2} ≤ 1.15942`. MATCHES, coefficients 24.31317 and 0.564016. -/
theorem eq_723_star {L S : ℝ} (hL : 0 ≤ L) (hS0 : 0 ≤ S) (hS : S ≤ 1.15942) :
    (1.414 / Real.log 2 * L + 2 * S / 49) * Real.log 150000 ≤ 24.32 * L + 0.57 := by
  have hr := log_150000_lt
  have hr0 := log_150000_pos
  have hl2 := Real.log_two_gt_d9
  have hl20 : 0 < Real.log 2 := by linarith
  have hc : 1.414 * Real.log 150000 / Real.log 2 ≤ 24.32 := by
    rw [div_le_iff₀ hl20]; nlinarith
  have hd : 2 * S / 49 * Real.log 150000 ≤ 0.57 := by
    have : 2 * S / 49 * Real.log 150000 ≤ 2 * 1.15942 / 49 * 11.918393 := by
      apply mul_le_mul (by linarith) hr.le hr0 (by norm_num)
    linarith
  have e : (1.414 / Real.log 2 * L + 2 * S / 49) * Real.log 150000 =
      (1.414 * Real.log 150000 / Real.log 2) * L + 2 * S / 49 * Real.log 150000 := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_right hc hL
  linarith

/-- (7.23), page 59, for `η+`: `(1.07996/log 2 · L + 2 · 1.19073) log r ≤ 18.57 L + 28.39`.
MATCHES, coefficients 18.569483 and 28.38317. -/
theorem eq_723_plus {L : ℝ} (hL : 0 ≤ L) :
    (1.07996 / Real.log 2 * L + 2 * 1.19073) * Real.log 150000 ≤ 18.57 * L + 28.39 := by
  have hr := log_150000_lt
  have hr0 := log_150000_pos
  have hl2 := Real.log_two_gt_d9
  have hl20 : 0 < Real.log 2 := by linarith
  have hc : 1.07996 * Real.log 150000 / Real.log 2 ≤ 18.57 := by
    rw [div_le_iff₀ hl20]; nlinarith
  have e : (1.07996 / Real.log 2 * L + 2 * 1.19073) * Real.log 150000 =
      (1.07996 * Real.log 150000 / Real.log 2) * L + 2 * 1.19073 * Real.log 150000 := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_right hc hL
  linarith

/-! ### The three error lines of (3.36) and (7.24) -/

/-- Page 60, first line of (3.36): with `|η◦|₂ ≤ 0.8001288` from (7.4), `ε₀|η◦|₂ ≤ 2.42942 · 10⁻⁶`
from (7.5), `|η◦⁽³⁾|₁ ≤ 32.5023` from (7.7), `δ₀ = 8`, `r = 150000`:
`2.82643 |η◦|₂²(2 + ε₀)ε₀ + (4.31004 |η◦|₂² + 0.0012 |η◦⁽³⁾|₁²/δ₀⁵)/r ≤ 2.9387 · 10⁻⁵`.
CONDITIONAL ON (7.4), (7.5), (7.7) as hypotheses. MATCHES, value 2.9386957e-5 with the paper's
rounded 2.43e-6, 0.80013, 4.3101, 32.503. -/
theorem const_29387 {e ε d3 : ℝ} (he0 : 0 ≤ e) (he : e ≤ 0.8001288) (hε0 : 0 ≤ ε)
    (h75 : ε * e ≤ 2.42942e-6) (hd0 : 0 ≤ d3) (hd : d3 ≤ 32.5023) :
    2.82643 * e ^ 2 * (2 + ε) * ε + (4.31004 * e ^ 2 + 0.0012 * d3 ^ 2 / 8 ^ 5) / 150000 ≤
      (2.9387e-5 : ℝ) := by
  have hεe0 : 0 ≤ ε * e := mul_nonneg hε0 he0
  have k1 : e ^ 2 * (2 + ε) * ε = (ε * e) * (2 * e + ε * e) := by ring
  have k2 : (ε * e) * (2 * e + ε * e) ≤ 2.43e-6 * (2 * 0.80013 + 2.43e-6) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have k3 : e ^ 2 ≤ (0.80013 : ℝ) ^ 2 := pow_le_pow_left₀ he0 (by linarith) 2
  have k4 : d3 ^ 2 ≤ (32.503 : ℝ) ^ 2 := pow_le_pow_left₀ hd0 (by linarith) 2
  have : (2.82643 : ℝ) * (2.43e-6 * (2 * 0.80013 + 2.43e-6)) +
      (4.31004 * 0.80013 ^ 2 + 0.0012 * 32.503 ^ 2 / 8 ^ 5) / 150000 ≤ 2.9387e-5 := by norm_num
  have k5 : 2.82643 * e ^ 2 * (2 + ε) * ε = 2.82643 * ((ε * e) * (2 * e + ε * e)) := by
    rw [mul_assoc, mul_assoc, ← mul_assoc (e ^ 2), k1]
  rw [k5]
  have : (4.31004 * e ^ 2 + 0.0012 * d3 ^ 2 / 8 ^ 5) / 150000 ≤
      (4.31004 * 0.80013 ^ 2 + 0.0012 * 32.503 ^ 2 / 8 ^ 5) / 150000 := by gcongr
  nlinarith

/-- Page 60: `|η*|₂² ≤ (3/(4κ)) (32/3)(log 2)³ (3/8)√π ≤ 1.77082/κ`, the constant part.
MATCHES, value 1.7708125. -/
theorem eta_star_two : 3 / 4 * (32 / 3) * Real.log 2 ^ 3 * (3 / 8) * Real.sqrt π ≤ (1.77082 : ℝ) := by
  have hl := Real.log_two_lt_d9
  have hl0 := Real.log_two_gt_d9
  have h3 : Real.log 2 ^ 3 ≤ (0.6931471808 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hl.le 3
  have hs : Real.sqrt π < 1.7724539 := by
    rw [Real.sqrt_lt' (by norm_num)]; have := Real.pi_lt_d20; linarith
  have hs0 := Real.sqrt_nonneg π
  have h30 : 0 ≤ Real.log 2 ^ 3 := by positivity
  have : Real.log 2 ^ 3 * Real.sqrt π ≤ 0.6931471808 ^ 3 * 1.7724539 :=
    mul_le_mul h3 hs.le hs0 (by norm_num)
  have : (3 : ℝ) / 4 * (32 / 3) * (0.6931471808 ^ 3 * 1.7724539) * (3 / 8) ≤ 1.77082 := by norm_num
  nlinarith

/-- Page 60, second line of (3.36): with `E_{η*} ≤ 1.9075 · 10⁻⁸/κ` (7.16),
`A_{η+} ≤ 8.7806` (7.8), `E_{η+} ≤ 2.3921 · 10⁻⁸` (7.2), `|η+|₂ ≤ 0.80014` (7.3),
`|η*|₂² ≤ 1.77082/κ`: `E_{η*}A + E_{η+} · 1.6812 (√A + 1.6812 |η+|₂)|η*|₂ ≤ 1.7815 · 10⁻⁶/κ`.
CONDITIONAL ON those inputs. MATCHES, value 1.7814779e-6. -/
theorem const_17815 {Es A Ep np ns : ℝ} (hEs0 : 0 ≤ Es) (hEs : Es ≤ 1.9075e-8 / κ)
    (hA0 : 0 ≤ A) (hA : A ≤ 8.7806) (hEp0 : 0 ≤ Ep) (hEp : Ep ≤ 2.3921e-8)
    (hnp0 : 0 ≤ np) (hnp : np ≤ 0.80014) (hns0 : 0 ≤ ns) (hns : ns ^ 2 ≤ 1.77082 / κ) :
    Es * A + Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) * ns ≤ (1.7815e-6 : ℝ) / κ := by
  unfold κ at *
  have hsA : Real.sqrt A ≤ 2.963209 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hsA0 := Real.sqrt_nonneg A
  have hns' : ns ≤ 0.1901033 := by
    by_contra hc; push_neg at hc
    have : (0.1901033 : ℝ) ^ 2 < ns ^ 2 := by
      exact pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    have : (1.77082 : ℝ) / 49 < 0.1901033 ^ 2 := by norm_num
    linarith
  have t1 : Es * A ≤ 1.9075e-8 / 49 * 8.7806 := mul_le_mul hEs hA hA0 (by norm_num)
  have t2 : Real.sqrt A + 1.6812 * np ≤ 2.963209 + 1.6812 * 0.80014 := by linarith
  have t3 : Ep * 1.6812 ≤ 2.3921e-8 * 1.6812 := by linarith
  have t4 : Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) ≤
      2.3921e-8 * 1.6812 * (2.963209 + 1.6812 * 0.80014) :=
    mul_le_mul t3 t2 (by positivity) (by norm_num)
  have t5 : Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) * ns ≤
      2.3921e-8 * 1.6812 * (2.963209 + 1.6812 * 0.80014) * 0.1901033 :=
    mul_le_mul t4 hns' hns0 (by norm_num)
  have : (1.9075e-8 : ℝ) / 49 * 8.7806 +
      2.3921e-8 * 1.6812 * (2.963209 + 1.6812 * 0.80014) * 0.1901033 ≤ 1.7815e-6 / 49 := by
    norm_num
  linarith

/-- QUESTION evidence, page 60: the text says it uses `A_{η+} ≤ 8.8013` "obtained in (7.8)", but
(7.8) prints `≤ 8.7806 x` and the displayed computation uses 8.7806. With `A = 8.8013` and the
other inputs at the paper's values, the second line EXCEEDS `1.7815 · 10⁻⁶/κ`: value
1.783180e-6/κ. PROVED. -/
theorem const_17815_with_88013 :
    (1.7815e-6 : ℝ) / κ < 1.9075e-8 / κ * 8.8013 +
      2.3921e-8 * 1.6812 * (Real.sqrt 8.8013 + 1.6812 * 0.80014) * Real.sqrt (1.77082 / κ) := by
  unfold κ
  have h1 : (2.9666 : ℝ) ≤ Real.sqrt 8.8013 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2 : (0.1901 : ℝ) ≤ Real.sqrt (1.77082 / 49) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have t : 2.3921e-8 * 1.6812 * (2.9666 + 1.6812 * 0.80014) * 0.1901 ≤
      2.3921e-8 * 1.6812 * (Real.sqrt 8.8013 + 1.6812 * 0.80014) * Real.sqrt (1.77082 / (49 : ℝ)) := by
    gcongr
  have : (1.7815e-6 : ℝ) / 49 < 1.9075e-8 / 49 * 8.8013 +
      2.3921e-8 * 1.6812 * (2.9666 + 1.6812 * 0.80014) * 0.1901 := by norm_num
  linarith

/-- Page 60, third line of (3.36): with `Z_{η+²,2} ≤ 0.640209 L` (7.17), `Z_{η*²,2} ≤ 0.0362 L`
(7.21), `LS_{η*} ≤ 24.32 L + 0.57`, `LS_{η+} ≤ 18.57 L + 28.39` (7.23) and `L = log x ≥ 34.5`:
`2 Z₊ LS* + 4 √(Z₊ Z*) LS₊ ≤ 43 L²`. CONDITIONAL ON those inputs. MATCHES, the coefficients
are 42.44780 L² + 18.01767 L, below 43 L² once L ≥ 32.63; the paper needs only x ≥ 10¹⁵. -/
theorem third_line_43 {L Zp Zs LSs LSp : ℝ} (hL : 34.5 ≤ L)
    (hZp0 : 0 ≤ Zp) (hZp : Zp ≤ 0.640209 * L) (hZs0 : 0 ≤ Zs) (hZs : Zs ≤ 0.0362 * L)
    (hLSs0 : 0 ≤ LSs) (hLSs : LSs ≤ 24.32 * L + 0.57) (hLSp0 : 0 ≤ LSp) (hLSp : LSp ≤ 18.57 * L + 28.39) :
    2 * Zp * LSs + 4 * Real.sqrt (Zp * Zs) * LSp ≤ 43 * L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hsq : Real.sqrt (Zp * Zs) ≤ 0.152236 * L := by
    rw [Real.sqrt_le_left (by positivity)]
    have : Zp * Zs ≤ (0.640209 * L) * (0.0362 * L) := mul_le_mul hZp hZs hZs0 (by positivity)
    nlinarith
  have hsq0 := Real.sqrt_nonneg (Zp * Zs)
  have t1 : Zp * LSs ≤ (0.640209 * L) * (24.32 * L + 0.57) := mul_le_mul hZp hLSs hLSs0 (by positivity)
  have t2 : Real.sqrt (Zp * Zs) * LSp ≤ (0.152236 * L) * (18.57 * L + 28.39) :=
    mul_le_mul hsq hLSp hLSp0 (by positivity)
  nlinarith

/-- `x ≥ 4.9 · 10²⁶` gives `log x ≥ 34.5`, far more than needed. -/
theorem log_x_ge {x : ℝ} (hx : 4.9e26 ≤ x) : 34.5 ≤ Real.log x := by
  have h : Real.log 1e15 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  have e : Real.log 1e15 = 15 * Real.log 10 := by
    rw [show (1e15 : ℝ) = 10 ^ 15 by norm_num, Real.log_pow]; push_cast; ring
  have := log_ten_gt_ratio
  have := Real.log_two_gt_d9
  linarith

/-- (7.24), page 60, assembled. CONDITIONAL ON the error shape of Proposition 3.2, display (3.36),
and on the inputs (7.2) to (7.8), (7.16), (7.17), (7.21), (7.23) as hypotheses: the three error
lines sum to at most `7.881 · 10⁻⁷ x²` for `x ≥ 4.9 · 10²⁶`, with `|η*|₁ = √(π/2)/κ` from (7.20). -/
theorem eq_724_assembled {x e ε d3 Es A Ep np ns Zp Zs LSs LSp : ℝ} (hx : 4.9e26 ≤ x)
    (he0 : 0 ≤ e) (he : e ≤ 0.8001288) (hε0 : 0 ≤ ε) (h75 : ε * e ≤ 2.42942e-6)
    (hd0 : 0 ≤ d3) (hd : d3 ≤ 32.5023)
    (hEs0 : 0 ≤ Es) (hEs : Es ≤ 1.9075e-8 / κ) (hA0 : 0 ≤ A) (hA : A ≤ 8.7806)
    (hEp0 : 0 ≤ Ep) (hEp : Ep ≤ 2.3921e-8) (hnp0 : 0 ≤ np) (hnp : np ≤ 0.80014)
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
  have h2 := const_17815 hEs0 hEs hA0 hA hEp0 hEp hnp0 hnp hns0 hns
  have h3 := third_line_43 (log_x_ge hx) hZp0 hZp hZs0 hZs hLSs0 hLSs hLSp0 hLSp
  have hm := major_err hx
  have hdv := major_err_div
  have hs0 : 0 ≤ Real.sqrt (π / 2) / κ * x ^ 2 := by positivity
  have hF0 : 0 ≤ 2.82643 * e ^ 2 * (2 + ε) * ε + (4.31004 * e ^ 2 + 0.0012 * d3 ^ 2 / 8 ^ 5) / 150000 := by
    positivity
  have b1 : (2.82643 * e ^ 2 * (2 + ε) * ε + (4.31004 * e ^ 2 + 0.0012 * d3 ^ 2 / 8 ^ 5) / 150000) *
      (Real.sqrt (π / 2) / κ) * x ^ 2 ≤ 2.9387e-5 * (Real.sqrt (π / 2) / κ * x ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hs0
  have b2 : (Es * A + Ep * 1.6812 * (Real.sqrt A + 1.6812 * np) * ns) * x ^ 2 ≤
      1.7815e-6 / κ * x ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
  have b3 : (2 * Zp * LSs + 4 * Real.sqrt (Zp * Zs) * LSp) * x ≤ 43 * Real.log x ^ 2 * x :=
    mul_le_mul_of_nonneg_right h3 hx0.le
  have key : 2.9387e-5 * (Real.sqrt (π / 2) / κ * x ^ 2) + 1.7815e-6 / κ * x ^ 2 +
      43 * Real.log x ^ 2 * x =
      (2.9387e-5 * Real.sqrt (π / 2) + 1.7815e-6 + κ * 43 * Real.log x ^ 2 / x) * (x ^ 2 / κ) := by
    field_simp
  have b4 : (2.9387e-5 * Real.sqrt (π / 2) + 1.7815e-6 + κ * 43 * Real.log x ^ 2 / x) * (x ^ 2 / κ) ≤
      3.8613e-5 * (x ^ 2 / κ) := mul_le_mul_of_nonneg_right hm (by positivity)
  have b5 : 3.8613e-5 * (x ^ 2 / κ) ≤ 7.881e-7 * x ^ 2 := by
    rw [show 3.8613e-5 * (x ^ 2 / κ) = (3.8613e-5 / κ) * x ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hdv (by positivity)
  linarith

/-! ### Vacuity: the hypotheses can hold -/

/-- One concrete instance of the hypotheses of `eq_724_assembled`: x = 4.9 · 10²⁶,
e = 0.8001287, ε = 0, d3 = 32.5023, A = 8.7806, np = 0.8, all other inputs 0. -/
theorem vacuity_724 :
    (2.82643 * 0.8001287 ^ 2 * (2 + 0) * 0 + (4.31004 * 0.8001287 ^ 2 + 0.0012 * 32.5023 ^ 2 / 8 ^ 5) / 150000) *
          (Real.sqrt (π / 2) / κ) * (4.9e26 : ℝ) ^ 2 +
        (0 * 8.7806 + 0 * 1.6812 * (Real.sqrt 8.7806 + 1.6812 * 0.8) * 0) * (4.9e26 : ℝ) ^ 2 +
        (2 * 0 * 0 + 4 * Real.sqrt (0 * 0) * 0) * (4.9e26 : ℝ) ≤ 7.881e-7 * (4.9e26 : ℝ) ^ 2 := by
  have hl := log_x_ge (le_refl (4.9e26 : ℝ))
  have hl0 : 0 ≤ Real.log 4.9e26 := by linarith
  exact eq_724_assembled (le_refl _) (by norm_num) (by norm_num) (le_refl _) (by norm_num)
    (by norm_num) (le_refl _) (le_refl _) (by unfold κ; norm_num) (by norm_num) (le_refl _)
    (le_refl _) (by norm_num) (by norm_num) (by norm_num) (le_refl _) (by unfold κ; norm_num)
    (le_refl _) (by linarith) (le_refl _) (by linarith) (le_refl _) (by linarith) (le_refl _)
    (by linarith)

/-- Vacuity of `eq_713`: `C = 1`, `P = √(π/2)`, `e₂ = 0.8001287²` meet its hypotheses. -/
theorem vacuity_713 :
    (1 / κ) * (Real.sqrt (π / 2) * 0.8001287 ^ 2 - 0.000834) ≤ (1 : ℝ) := by
  have hs := sqrt_pi_half_lt
  have hE := (Real.exp_pos (-(2 * κ ^ 2))).le
  apply eq_713 (by norm_num) (by norm_num)
  unfold κ at *
  have : (1 / 49 : ℝ) * Real.sqrt (π / 2) * 0.8001287 ^ 2 ≤ 1 := by nlinarith
  have : 0 ≤ (0.8001287 : ℝ) ^ 2 * (2 + 1 / 49 ^ 2) * Real.exp (-(2 * 49 ^ 2)) := by positivity
  have : (0 : ℝ) ≤ 2.0002 / 49 ^ 3 := by norm_num
  linarith

end LeanLab.Helfgott2013

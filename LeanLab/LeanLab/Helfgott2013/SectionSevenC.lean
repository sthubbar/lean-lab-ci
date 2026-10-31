/-
P0001 Helfgott 2013, arXiv 1312.7748v2, Section 7.3, pages 64 to 67: the constants that need
Euler's constant or a monotonicity argument, left open by U-5008.
- page 64: `F(r₀) = e^γ log log r₀ + 2.50637/log log r₀ ≤ 5.42506`, `r₀ = 150000`, margin 3.5e-7;
- page 64: `L_{r₀} ≤ 394.316` and `g(r₀) ≤ 0.041014` for `y ≥ 10²⁵`;
- (7.40), page 65: `F(y^{4/15}) ≤ e^γ log log y - 1.43644` for `y ≥ 10²⁵`, margin 2.6e-6;
- (7.41), pages 66 and 67: the coefficient `7/15 · 0.30782 ≤ 0.14365`, the shift
  `0.640209 log 49 - 0.021095 ≤ 2.4705`, and
  `0.14365 log y √(log log y) (0.640209 log y + 2.4705) / y^{2/15} ≤ 0.30386` for every
  `y ≥ 10²⁵`, by a monotonicity argument from `1 + x ≤ eˣ`, margin 2.5e-6;
- (7.42), page 67: `I_{1,r₀} = F(log r₀) + 2e^γ/log r₀ ≤ 5.73827`, `F(t) = e^γ log t + 1.025742`.
Formulas read from the rendered page images of pages 64 to 67.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is Helfgott's theorem.
-/
import Mathlib
import LeanLab.Helfgott2013.GammaFine
import LeanLab.Helfgott2013.SectionSeven

open Real Finset

noncomputable section
namespace LeanLab.Helfgott2013.SectionSevenC

open LeanLab.ChenExplicit.Gamma LeanLab.Helfgott2013.GammaFine

/-! ### Logarithms of small rationals -/

theorem l32_lo : (0.4054651080 : ℝ) < log (3 / 2) := log_three_halves_gt

theorem l32_hi : log (3 / 2) < (0.4054651082 : ℝ) := by
  have h := log_one_add_inv_le_sum (a := (2 : ℝ)) (by norm_num) 8
  simp only [sum_range_succ, sum_range_zero] at h
  rw [show (1 : ℝ) + (2 : ℝ)⁻¹ = 3 / 2 by norm_num] at h
  norm_num at h
  linarith

theorem l54_lo : (0.2231435513 : ℝ) < log (5 / 4) := by
  have h := log_one_add_inv_ge_sum (a := (4 : ℝ)) (by norm_num) 6
  simp only [sum_range_succ, sum_range_zero] at h
  rw [show (1 : ℝ) + (4 : ℝ)⁻¹ = 5 / 4 by norm_num] at h
  norm_num at h
  linarith

theorem l54_hi : log (5 / 4) < (0.2231435514 : ℝ) := by
  have h := log_one_add_inv_le_sum (a := (4 : ℝ)) (by norm_num) 6
  simp only [sum_range_succ, sum_range_zero] at h
  rw [show (1 : ℝ) + (4 : ℝ)⁻¹ = 5 / 4 by norm_num] at h
  norm_num at h
  linarith

/-- `log 150000 = 15 log 2 + log(3/2) + 5 log(5/4)`. -/
theorem log_r0_eq : log (150000 : ℝ) = 15 * log 2 + log (3 / 2) + 5 * log (5 / 4) := by
  have : (150000 : ℝ) = 2 ^ 15 * (3 / 2) * (5 / 4) ^ 5 := by norm_num
  rw [this, log_mul (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num), log_pow,
    log_pow]
  push_cast; ring

theorem log_r0_bounds : (11.918390569 : ℝ) < log 150000 ∧ log (150000 : ℝ) < 11.918390578 := by
  rw [log_r0_eq]
  have := log_two_gt_d9; have := log_two_lt_d9
  have := l32_lo; have := l32_hi; have := l54_lo; have := l54_hi
  constructor <;> linarith

/-- `log 12 = 3 log 2 + log(3/2)`. -/
theorem log_12_eq : log (12 : ℝ) = 3 * log 2 + log (3 / 2) := by
  have : (12 : ℝ) = 2 ^ 3 * (3 / 2) := by norm_num
  rw [this, log_mul (by norm_num) (by norm_num), log_pow]; push_cast; ring

/-- `log 64 = 6 log 2`. -/
theorem log_64_eq : log (64 : ℝ) = 6 * log 2 := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]; push_cast; ring

/-- `log U = log B - log(1 + 1/a)` with `a = U/(B - U)`, for `0 < U < B`. -/
theorem log_via {U B : ℝ} (hU : 0 < U) (hUB : U < B) :
    log U = log B - log (1 + (U / (B - U))⁻¹) := by
  have hB : 0 < B := by linarith
  have e : 1 + (U / (B - U))⁻¹ = B / U := by
    rw [inv_div]; field_simp; ring
  rw [e, log_div hB.ne' hU.ne']; ring

/-! ### `u = log log r₀` -/

theorem u_hi : log (log (150000 : ℝ)) < 2.4780826372 := by
  have hL := log_r0_bounds
  have h1 : log (log (150000 : ℝ)) ≤ log (11.918390578 : ℝ) :=
    log_le_log (by linarith) hL.2.le
  rw [log_via (by norm_num) (by norm_num : (11.918390578 : ℝ) < 12), log_12_eq] at h1
  have hs := log_one_add_inv_ge_sum
    (a := (11.918390578 : ℝ) / (12 - 11.918390578)) (by norm_num) 3
  simp only [sum_range_succ, sum_range_zero] at hs
  norm_num at hs
  have := log_two_lt_d9; have := l32_hi
  norm_num at h1 ⊢
  linarith

theorem u_lo : (2.478082631 : ℝ) < log (log (150000 : ℝ)) := by
  have hL := log_r0_bounds
  have h1 : log (11.918390569 : ℝ) ≤ log (log (150000 : ℝ)) :=
    log_le_log (by norm_num) hL.1.le
  rw [log_via (by norm_num) (by norm_num : (11.918390569 : ℝ) < 12), log_12_eq] at h1
  have hs := log_one_add_inv_le_sum
    (a := (11.918390569 : ℝ) / (12 - 11.918390569)) (by norm_num) 3
  simp only [sum_range_succ, sum_range_zero] at hs
  norm_num at hs
  have := log_two_gt_d9; have := l32_lo
  norm_num at h1 ⊢
  linarith

/-- **Page 64: `F(r₀) = e^γ log log r₀ + 2.50637 / log log r₀ ≤ 5.42506`**, `r₀ = 150000`.
MATCHES; the true value is `5.4250596…`, margin `3.5 · 10⁻⁷`. -/
theorem F_r0 : exp eulerMascheroniConstant * log (log (150000 : ℝ)) +
    2.50637 / log (log (150000 : ℝ)) ≤ 5.42506 := by
  have hE := exp_gamma_lt
  have h1 := u_hi; have h2 := u_lo
  set u := log (log (150000 : ℝ))
  have hu : 0 < u := by linarith
  have hE0 : 0 < exp eulerMascheroniConstant := exp_pos _
  have a1 : exp eulerMascheroniConstant * u ≤ 1.7810725 * 2.4780826372 := by
    apply mul_le_mul hE.le h1.le hu.le (by norm_num)
  have a2 : 2.50637 / u ≤ 2.50637 / 2.478082631 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2.le
  have : (1.7810725 : ℝ) * 2.4780826372 + 2.50637 / 2.478082631 ≤ 5.42506 := by norm_num
  linarith

/-- **(7.42): `I_{1,r₀} = e^γ log log r₀ + 1.025742 + 2 e^γ / log r₀ ≤ 5.73827`**; the paper
prints `= 5.73826…`, true value `5.7382646…`, MATCH; the upper bound is what (7.46) uses. -/
theorem I1_r0 : exp eulerMascheroniConstant * log (log (150000 : ℝ)) + 1.025742 +
    2 * exp eulerMascheroniConstant / log (150000 : ℝ) ≤ 5.73827 := by
  have hE := exp_gamma_lt
  have h1 := u_hi
  have hL := log_r0_bounds
  have hE0 : 0 < exp eulerMascheroniConstant := exp_pos _
  have hu : 0 < log (log (150000 : ℝ)) := by have := u_lo; linarith
  have a1 : exp eulerMascheroniConstant * log (log (150000 : ℝ)) ≤ 1.7810725 * 2.4780826372 :=
    mul_le_mul hE.le h1.le hu.le (by norm_num)
  have a2 : 2 * exp eulerMascheroniConstant / log (150000 : ℝ) ≤ 2 * 1.7810725 / 11.918390569 :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hL.1.le
  have : (1.7810725 : ℝ) * 2.4780826372 + 1.025742 + 2 * 1.7810725 / 11.918390569 ≤ 5.73827 := by
    norm_num
  linarith

/-! ### `L_{r₀}` and `g(r₀)`, page 64 -/

/-- **`L_{r₀} ≤ 394.316`**, page 64. MATCHES; true value `394.31535…`. -/
theorem L_r0 : 5.42506 * (log ((2 : ℝ) ^ (7 / 4 : ℝ) * 150000 ^ (13 / 4 : ℝ)) + 80 / 9) +
    log ((2 : ℝ) ^ (16 / 9 : ℝ) * 150000 ^ (80 / 9 : ℝ)) + 111 / 5 ≤ 394.316 := by
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_rpow (by norm_num), log_rpow (by norm_num), log_rpow (by norm_num),
    log_rpow (by norm_num)]
  have hL := log_r0_bounds
  have := log_two_lt_d9
  nlinarith

theorem sqrt_542506_le : sqrt (5.42506 : ℝ) ≤ 2.329176 := by
  rw [sqrt_le_left (by norm_num)]; norm_num

theorem sqrt_300000_ge : (547.7225 : ℝ) ≤ sqrt (2 * 150000) := by
  rw [le_sqrt (by norm_num) (by norm_num)]; norm_num

/-- `(log y / (2y))^{1/6} ≤ 1.19270 · 10⁻⁴` for `y ≥ 10²⁵`. -/
theorem tail_sixth {y : ℝ} (hy : 1e25 ≤ y) :
    (log y / (2 * y)) ^ (1 / 6 : ℝ) ≤ 1.19270e-4 := by
  have hy0 : 0 < y := by linarith
  have he : exp 1 ≤ (1e25 : ℝ) := by
    have := exp_one_lt_d9; linarith
  have hanti := Real.log_div_self_antitoneOn (Set.mem_setOf.2 he)
    (Set.mem_setOf.2 (le_trans he hy)) hy
  have hlog25 : log (1e25 : ℝ) = 25 * log 10 := by
    rw [show (1e25 : ℝ) = 10 ^ 25 by norm_num, log_pow]; push_cast; ring
  have hl10 := LeanLab.Helfgott2013.log_ten_lt
  have hz : log y / (2 * y) ≤ 57.56465 / (2 * 1e25) := by
    have : log y / (2 * y) = (log y / y) / 2 := by field_simp
    rw [this]
    have h2 : log (1e25 : ℝ) / 1e25 ≤ 57.56465 / 1e25 := by
      rw [hlog25]; apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    have : (57.56465 : ℝ) / (2 * 1e25) = (57.56465 / 1e25) / 2 := by ring
    rw [this]; linarith
  have hz0 : 0 ≤ log y / (2 * y) := div_nonneg (log_nonneg (by linarith)) (by linarith)
  calc (log y / (2 * y)) ^ (1 / 6 : ℝ) ≤ (57.56465 / (2 * 1e25) : ℝ) ^ (1 / 6 : ℝ) :=
        rpow_le_rpow hz0 hz (by norm_num)
    _ ≤ ((1.19270e-4 : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) := by
        apply rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = 1.19270e-4 := by
        rw [← rpow_natCast, ← rpow_mul (by norm_num)]; norm_num

/-- **`g(r₀) ≤ 0.041014`** for `y ≥ 10²⁵`, page 64. MATCHES; value `0.04101304…` at `10²⁵`. -/
theorem g_r0 {y : ℝ} (hy : 1e25 ≤ y) :
    ((0.58385 * log 300000 + 0.5) * sqrt 5.42506 + 2.5) / sqrt (2 * 150000) + 394.316 / 150000 +
      3.2 * (log y / (2 * y)) ^ (1 / 6 : ℝ) ≤ 0.041014 := by
  have hL := log_r0_bounds
  have h3 : log (300000 : ℝ) = log 150000 + log 2 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := log_two_lt_d9
  have hl : log (300000 : ℝ) ≤ 12.6115378 := by rw [h3]; linarith
  have hl0 : 0 ≤ log (300000 : ℝ) := log_nonneg (by norm_num)
  have hs := sqrt_542506_le
  have hs0 : 0 ≤ sqrt (5.42506 : ℝ) := sqrt_nonneg _
  have hq := sqrt_300000_ge
  have ht := tail_sixth hy
  have hnum : (0.58385 * log 300000 + 0.5) * sqrt 5.42506 + 2.5 ≤
      (0.58385 * 12.6115378 + 0.5) * 2.329176 + 2.5 := by
    have : 0.58385 * log 300000 + 0.5 ≤ 0.58385 * 12.6115378 + 0.5 := by linarith
    nlinarith
  have hnum0 : 0 ≤ (0.58385 * log 300000 + 0.5) * sqrt 5.42506 + 2.5 := by positivity
  have hfrac : ((0.58385 * log 300000 + 0.5) * sqrt 5.42506 + 2.5) / sqrt (2 * 150000) ≤
      ((0.58385 * 12.6115378 + 0.5) * 2.329176 + 2.5) / 547.7225 :=
    div_le_div₀ (by norm_num) hnum (by norm_num) hq
  have : ((0.58385 * 12.6115378 + 0.5) * 2.329176 + 2.5) / 547.7225 + 394.316 / 150000 +
      3.2 * 1.19270e-4 ≤ (0.041014 : ℝ) := by norm_num
  linarith

/-! ### (7.40), page 65 -/

theorem l154_bounds : (1.3217558396 : ℝ) < log (15 / 4) ∧ log (15 / 4 : ℝ) < 1.3217558404 := by
  have e : log (15 / 4 : ℝ) = log 2 + log (3 / 2) + log (5 / 4) := by
    rw [← log_mul (by norm_num) (by norm_num), ← log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  have := log_two_gt_d9; have := log_two_lt_d9
  have := l32_lo; have := l32_hi; have := l54_lo; have := l54_hi
  constructor <;> linarith

theorem t0_bounds : (57.564627305 : ℝ) ≤ 25 * log 10 ∧ 25 * log 10 ≤ (57.56462808 : ℝ) := by
  have e : log (10 : ℝ) = 3 * log 2 + log (5 / 4) := by
    rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num, log_mul (by norm_num) (by norm_num),
      log_pow]; push_cast; ring
  rw [e]
  have := log_two_gt_d9; have := log_two_lt_d9; have := l54_lo; have := l54_hi
  constructor <;> linarith

/-- `log log y ≥ 4.0529081` for `y ≥ 10²⁵`. -/
theorem lly_lo {y : ℝ} (hy : 1e25 ≤ y) : (4.0529081 : ℝ) ≤ log (log y) := by
  have hlog25 : log (1e25 : ℝ) = 25 * log 10 := by
    rw [show (1e25 : ℝ) = 10 ^ 25 by norm_num, log_pow]; push_cast; ring
  have ht := t0_bounds
  have hly : (57.564627305 : ℝ) ≤ log y := by
    have := log_le_log (by norm_num) hy; linarith
  have h1 : log (57.564627305 : ℝ) ≤ log (log y) := log_le_log (by norm_num) hly
  rw [log_via (by norm_num) (by norm_num : (57.564627305 : ℝ) < 64), log_64_eq] at h1
  have hs := log_one_add_inv_le_sum
    (a := (57.564627305 : ℝ) / (64 - 57.564627305)) (by norm_num) 6
  simp only [sum_range_succ, sum_range_zero] at hs
  norm_num at hs
  have := log_two_gt_d9
  norm_num at h1 ⊢
  linarith

/-- `log log y^{4/15} = log log y - log(15/4)` for `y > 1`. -/
theorem lly_415 {y : ℝ} (hy : 1 < y) :
    log (log (y ^ (4 / 15 : ℝ))) = log (log y) - log (15 / 4) := by
  have hy0 : 0 < y := by linarith
  have hl : 0 < log y := log_pos hy
  rw [log_rpow hy0, log_mul (by norm_num) hl.ne']
  rw [show (4 / 15 : ℝ) = (15 / 4)⁻¹ by norm_num, log_inv]; ring

/-- **(7.40): `F(y^{4/15}) ≤ e^γ log log y - 1.43644` for `y ≥ 10²⁵`**, where
`F(r) = e^γ log log r + 2.50637/log log r`. MATCHES; value `-1.436446…` at `10²⁵`. -/
theorem F_740 {y : ℝ} (hy : 1e25 ≤ y) :
    exp eulerMascheroniConstant * log (log (y ^ (4 / 15 : ℝ))) +
      2.50637 / log (log (y ^ (4 / 15 : ℝ))) ≤
      exp eulerMascheroniConstant * log (log y) - 1.43644 := by
  rw [lly_415 (by linarith)]
  have hE := exp_gamma_gt
  have hll := lly_lo hy
  have hc := l154_bounds
  have hd : (2.7311522 : ℝ) ≤ log (log y) - log (15 / 4) := by linarith
  have h1 : 2.50637 / (log (log y) - log (15 / 4)) ≤ 2.50637 / 2.7311522 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
  have h2 : 1.7810699 * 1.3217558396 ≤ exp eulerMascheroniConstant * log (15 / 4) :=
    mul_le_mul hE.le hc.1.le (by norm_num) (exp_pos _).le
  have : (2.50637 : ℝ) / 2.7311522 - 1.7810699 * 1.3217558396 ≤ -1.43644 := by norm_num
  nlinarith

/-! ### (7.41), pages 66 and 67 -/

/-- `7/15 · 0.30782 ≤ 0.14365`. MATCHES. -/
theorem coeff_741 : (7 / 15 : ℝ) * 0.30782 ≤ 0.14365 := by norm_num

/-- `0.640209 log x - 0.021095 ≤ 0.640209 log y + 2.4705` for `x = 49 y`. MATCHES. -/
theorem shift_741 {y : ℝ} (hy : 0 < y) :
    0.640209 * log (49 * y) - 0.021095 ≤ 0.640209 * log y + 2.4705 := by
  rw [log_mul (by norm_num) hy.ne']
  have := LeanLab.Helfgott2013.log_49_lt
  nlinarith

/-- The monotonicity step: for `t ≥ t₀ > 1`, `φ(t) ≤ φ(t₀)` where
`φ(t) = t √(log t) (a t + b) e^{-2t/15}`, as soon as
`1/t₀ + a/(a t₀ + b) + 1/(2 t₀ log t₀) ≤ 2/15`. Uses only `1 + x ≤ eˣ`. -/
theorem phi_le {t t₀ a b : ℝ} (ht₀ : 1 < t₀) (ht : t₀ ≤ t) (ha : 0 ≤ a) (hb : 0 < b)
    (hk : 1 / t₀ + a / (a * t₀ + b) + 1 / (2 * t₀ * log t₀) ≤ 2 / 15) :
    t * sqrt (log t) * (a * t + b) * exp (-(2 * t / 15)) ≤
      t₀ * sqrt (log t₀) * (a * t₀ + b) * exp (-(2 * t₀ / 15)) := by
  set s := t - t₀ with hs
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 < t₀ := by linarith
  have hl0 : 0 < log t₀ := log_pos ht₀
  have hA : 0 < a * t₀ + b := by positivity
  -- t ≤ t₀ e^{s/t₀}
  have h1 : t ≤ t₀ * exp (s / t₀) := by
    have := add_one_le_exp (s / t₀)
    have e : t = t₀ * (s / t₀ + 1) := by field_simp; ring
    rw [e]; exact mul_le_mul_of_nonneg_left this ht0.le
  -- a t + b ≤ (a t₀ + b) e^{a s/(a t₀ + b)}
  have h2 : a * t + b ≤ (a * t₀ + b) * exp (a * s / (a * t₀ + b)) := by
    have := add_one_le_exp (a * s / (a * t₀ + b))
    have e : a * t + b = (a * t₀ + b) * (a * s / (a * t₀ + b) + 1) := by field_simp; ring
    rw [e]; exact mul_le_mul_of_nonneg_left this hA.le
  -- log t ≤ log t₀ e^{s/(t₀ log t₀)}
  have h3 : log t ≤ log t₀ * exp (s / (t₀ * log t₀)) := by
    have hlt : log t ≤ log t₀ + s / t₀ := by
      have e : log t = log t₀ + log (t / t₀) := by
        rw [log_div (by linarith) ht0.ne']; ring
      have := log_le_sub_one_of_pos (div_pos (show (0 : ℝ) < t by linarith) ht0)
      have e2 : t / t₀ - 1 = s / t₀ := by rw [hs]; field_simp
      linarith
    have := add_one_le_exp (s / (t₀ * log t₀))
    have e : log t₀ + s / t₀ = log t₀ * (s / (t₀ * log t₀) + 1) := by field_simp; ring
    rw [e] at hlt
    exact le_trans hlt (mul_le_mul_of_nonneg_left this hl0.le)
  have h3' : sqrt (log t) ≤ sqrt (log t₀) * exp (s / (2 * t₀ * log t₀)) := by
    have hsq : exp (s / (t₀ * log t₀)) = exp (s / (2 * t₀ * log t₀)) ^ 2 := by
      rw [← exp_nat_mul]; congr 1; push_cast; field_simp
    rw [hsq] at h3
    calc sqrt (log t) ≤ sqrt (log t₀ * exp (s / (2 * t₀ * log t₀)) ^ 2) := sqrt_le_sqrt h3
      _ = sqrt (log t₀) * exp (s / (2 * t₀ * log t₀)) := by
          rw [sqrt_mul hl0.le, sqrt_sq (exp_pos _).le]
  have h4 : exp (-(2 * t / 15)) = exp (-(2 * t₀ / 15)) * exp (-(2 * s / 15)) := by
    rw [← exp_add]; congr 1; rw [hs]; ring
  have hsqt : 0 ≤ sqrt (log t) := sqrt_nonneg _
  have hT : 0 ≤ t := by linarith
  have hAt : 0 ≤ a * t + b := by nlinarith
  calc t * sqrt (log t) * (a * t + b) * exp (-(2 * t / 15))
      ≤ (t₀ * exp (s / t₀)) * (sqrt (log t₀) * exp (s / (2 * t₀ * log t₀))) *
          ((a * t₀ + b) * exp (a * s / (a * t₀ + b))) * exp (-(2 * t / 15)) := by
        gcongr
    _ = t₀ * sqrt (log t₀) * (a * t₀ + b) * exp (-(2 * t₀ / 15)) *
          exp (s * (1 / t₀ + a / (a * t₀ + b) + 1 / (2 * t₀ * log t₀) - 2 / 15)) := by
        rw [h4]
        have : s * (1 / t₀ + a / (a * t₀ + b) + 1 / (2 * t₀ * log t₀) - 2 / 15) =
            s / t₀ + s / (2 * t₀ * log t₀) + a * s / (a * t₀ + b) + -(2 * s / 15) := by ring
        rw [this, exp_add, exp_add, exp_add]; ring
    _ ≤ t₀ * sqrt (log t₀) * (a * t₀ + b) * exp (-(2 * t₀ / 15)) * 1 := by
        gcongr
        rw [exp_le_one_iff]
        exact mul_nonpos_of_nonneg_of_nonpos hs0 (by linarith)
    _ = _ := mul_one _

/-- **(7.41): `0.14365 log y √(log log y) (0.640209 log y + 2.4705) / y^{2/15} ≤ 0.30386`
for every `y ≥ 10²⁵`.** MATCHES; value `0.3038560…` at `y = 10²⁵`, margin `4 · 10⁻⁶`. -/
theorem bound_741 {y : ℝ} (hy : 1e25 ≤ y) :
    0.14365 * log y * sqrt (log (log y)) * (0.640209 * log y + 2.4705) / y ^ (2 / 15 : ℝ) ≤
      0.30386 := by
  have hy0 : 0 < y := by linarith
  set t₀ : ℝ := 25 * log 10 with ht₀
  have hlog25 : log (1e25 : ℝ) = t₀ := by
    rw [show (1e25 : ℝ) = 10 ^ 25 by norm_num, log_pow]; push_cast; ring
  have hb := t0_bounds
  have ht : t₀ ≤ log y := by rw [← hlog25]; exact log_le_log (by norm_num) hy
  have hrp : y ^ (2 / 15 : ℝ) = exp (2 * log y / 15) := by
    rw [rpow_def_of_pos hy0]; ring_nf
  -- log t₀ bounds
  have hlt0 : (4.05 : ℝ) ≤ log t₀ := by
    have := lly_lo (le_refl (1e25 : ℝ)); rw [hlog25] at this; linarith
  have hlt1 : log t₀ ≤ 4.0529087 := by
    have h1 : log t₀ ≤ log (57.56462808 : ℝ) := log_le_log (by linarith) hb.2
    rw [log_via (by norm_num) (by norm_num : (57.56462808 : ℝ) < 64), log_64_eq] at h1
    have hs := log_one_add_inv_ge_sum
      (a := (57.56462808 : ℝ) / (64 - 57.56462808)) (by norm_num) 3
    simp only [sum_range_succ, sum_range_zero] at hs
    norm_num at hs
    have := log_two_lt_d9
    norm_num at h1 ⊢
    linarith
  have hk : 1 / t₀ + 0.640209 / (0.640209 * t₀ + 2.4705) + 1 / (2 * t₀ * log t₀) ≤ 2 / 15 := by
    have e1 : 1 / t₀ ≤ 1 / 57 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have e2 : 0.640209 / (0.640209 * t₀ + 2.4705) ≤ 0.640209 / 38 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    have e3 : 1 / (2 * t₀ * log t₀) ≤ 1 / 400 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    have : (1 : ℝ) / 57 + 0.640209 / 38 + 1 / 400 ≤ 2 / 15 := by norm_num
    linarith
  have hphi := phi_le (t := log y) (t₀ := t₀) (a := 0.640209) (b := 2.4705)
    (by linarith) ht (by norm_num) (by norm_num) hk
  -- value at t₀: e^{2t₀/15} = 10^{10/3} ≥ 2154.43
  have hE : (2154.43 : ℝ) ≤ exp (2 * t₀ / 15) := by
    have h3 : exp (2 * t₀ / 15) ^ 3 = 10 ^ 10 := by
      rw [← exp_nat_mul, ht₀]
      rw [show ((3 : ℕ) : ℝ) * (2 * (25 * log 10) / 15) = 10 * log 10 by push_cast; ring]
      rw [show (10 : ℝ) * log 10 = log (10 ^ 10) by rw [log_pow]; push_cast; ring,
        exp_log (by positivity)]
    by_contra hc
    push Not at hc
    have : exp (2 * t₀ / 15) ^ 3 < (2154.43 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hc (exp_pos _).le (by norm_num)
    rw [h3] at this; norm_num at this
  have hsq : sqrt (log t₀) ≤ 2.013187 := by
    rw [sqrt_le_left (by norm_num)]; nlinarith
  have hval : 0.14365 * (t₀ * sqrt (log t₀) * (0.640209 * t₀ + 2.4705) * exp (-(2 * t₀ / 15))) ≤
      0.30386 := by
    rw [exp_neg]
    have hEi : (exp (2 * t₀ / 15))⁻¹ ≤ 1 / 2154.43 := by
      rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hE
    have hsq0 : 0 ≤ sqrt (log t₀) := sqrt_nonneg _
    have hA : t₀ * sqrt (log t₀) * (0.640209 * t₀ + 2.4705) ≤
        57.56462808 * 2.013187 * (0.640209 * 57.56462808 + 2.4705) := by
      have h1 : t₀ * sqrt (log t₀) ≤ 57.56462808 * 2.013187 :=
        mul_le_mul hb.2 hsq hsq0 (by norm_num)
      have h2 : 0.640209 * t₀ + 2.4705 ≤ 0.640209 * 57.56462808 + 2.4705 := by linarith
      exact mul_le_mul h1 h2 (by linarith) (by positivity)
    have hA0 : 0 ≤ t₀ * sqrt (log t₀) * (0.640209 * t₀ + 2.4705) := by
      have : 0 ≤ t₀ := by linarith
      positivity
    have : 0.14365 * (57.56462808 * 2.013187 * (0.640209 * 57.56462808 + 2.4705) *
        (1 / 2154.43)) ≤ (0.30386 : ℝ) := by norm_num
    have hm := mul_le_mul hA hEi (inv_nonneg.2 (exp_pos _).le) (by positivity)
    nlinarith
  rw [hrp, div_eq_mul_inv, ← exp_neg]
  have e : 0.14365 * log y * sqrt (log (log y)) * (0.640209 * log y + 2.4705) *
      exp (-(2 * log y / 15)) =
      0.14365 * (log y * sqrt (log (log y)) * (0.640209 * log y + 2.4705) *
        exp (-(2 * log y / 15))) := by ring
  rw [e]
  nlinarith

end LeanLab.Helfgott2013.SectionSevenC

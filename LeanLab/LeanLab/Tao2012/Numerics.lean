/-
Tao 2012, Section 8, the explicit constants, checked against arXiv 1201.6656v4.
Read 2026-10-18 by run 20261018T0503Z-16389 through Claude in Chrome.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.

Every theorem here is plain arithmetic on the numbers the paper prints. Two printed
steps do not follow from the printed inputs; see `A2_gt_330`, `S0_error_exceeds` and
`eq815_exceeds`. The main result is not affected; see FINDINGS.md.
-/
import Mathlib

namespace LeanLab.Tao2012.Numerics

/-- `T0 = 3.29 · 10^9`, Theorem 1.5. -/
noncomputable def T0 : ℝ := 3.29e9
/-- `N0 = 4 · 10^14`, Theorem 1.6. -/
noncomputable def N0 : ℝ := 4e14
/-- `N(T0) ≤ 10^10`, the zero count Tao uses. -/
noncomputable def NT0 : ℝ := 1e10
/-- `K = 10^3`. -/
noncomputable def K : ℝ := 1e3

/-- Proposition 7.2, (7.4): `A = 60 ‖η‖₁ + 32 c' ‖η'‖₁ + 4 c'^2 ‖η''‖₁`. -/
noncomputable def Aconst (l1 d1 d2 c' : ℝ) : ℝ := 60 * l1 + 32 * c' * d1 + 4 * c' ^ 2 * d2

/-- p. 8.x: `A₁ = 229.2` from (8.4), (8.6), (8.8) with `c₁' = 0.9`: `‖η₁‖₁ = 7/10`,
`‖η₁'‖₁ = 2`, `‖η₁''‖₁ = 40`. MATCHES the paper. -/
theorem A1_eq : Aconst (7 / 10) 2 40 (9 / 10) = 229.2 := by
  unfold Aconst; norm_num

/-- `A₂` for `η₀`, `c' = 1`, from (5.9) `‖η₀‖₁ = 1`, (5.11) `‖η₀'‖₁ = 8 log 2`,
(5.13) `‖η₀''‖₁ = 48`: `A₂ = 252 + 256 log 2`. MATCHES the paper's closed form. -/
theorem A2_eq : Aconst 1 (8 * Real.log 2) 48 1 = 252 + 256 * Real.log 2 := by
  unfold Aconst; ring

/-- FINDING: the paper prints `A₂ = 252 + 256 log 2 ≤ 330`. In fact `252 + 256 log 2 > 429`. -/
theorem A2_gt_330 : (330 : ℝ) < 252 + 256 * Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

theorem A2_gt_429 : (429 : ℝ) < 252 + 256 * Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- With the paper's own `A₂ ≤ 330` the printed bound does hold; the slip matters only
because the true `A₂` is larger. Lower bound `log T0 > 31 log 2` used below. -/
theorem log_T0_gt : 21.48 < Real.log T0 := by
  have h2 := Real.log_two_gt_d9
  have h : (2 : ℝ) ^ 31 < T0 := by unfold T0; norm_num
  have h' : Real.log ((2 : ℝ) ^ 31) < Real.log T0 :=
    Real.log_lt_log (by positivity) h
  rw [Real.log_pow] at h'
  push_cast at h'
  linarith

/-- The second term of (7.3) for `η₀` at `x/K`, divided by `x/K`, without the factor
`c^{-1/2} = 2` that (7.3) carries for `c = 1/4`, exactly as printed:
`2.01 · (K/x)^{1/2} · N(T0) · ‖η₀‖₁`. At `x = 8.7 · 10^36` it exceeds `2.1 · 10^-7`. -/
theorem second_term_gt : 2.1e-7 < 2.01 * Real.sqrt (K / 8.7e36) * NT0 * 1 := by
  have hs : (1.06e-17 : ℝ) < Real.sqrt (K / 8.7e36) := by
    rw [Real.lt_sqrt (by norm_num)]; unfold K; norm_num
  unfold NT0; nlinarith

/-- FINDING: with the true `A₂ = 252 + 256 log 2`, the printed error terms of Proposition 7.2
for `S_{η₀,1}(x/K, α)` at `x = 8.7 · 10^36`, `K = 10^3`, `T0 = 3.29 · 10^9`,
`N(T0) = 10^10` sum to more than `10^-6`, so the printed conclusion
`S_{η₀,1}(x/K, α) = (x/K)(η̂₀(αx/K) + O*(10^-6))` does not follow at the bottom of the range.
This holds even without the factor `c^{-1/2} = 2`, which would make the excess larger. -/
theorem S0_error_exceeds :
    (1e-6 : ℝ) < (252 + 256 * Real.log 2) * Real.log T0 / (3 * T0) +
      2.01 * Real.sqrt (K / 8.7e36) * NT0 * 1 := by
  have h2 := Real.log_two_gt_d9
  have hT := log_T0_gt
  have hs := second_term_gt
  have hA : (429 : ℝ) < 252 + 256 * Real.log 2 := by linarith
  have h1 : (429 : ℝ) * 21.48 / (3 * T0) < (252 + 256 * Real.log 2) * Real.log T0 / (3 * T0) := by
    apply div_lt_div_of_pos_right _ (by unfold T0; norm_num)
    nlinarith
  have h3 : (9.33e-7 : ℝ) < 429 * 21.48 / (3 * T0) := by unfold T0; norm_num
  linarith

/-- The printed bound with the paper's value `A₂ = 330` is under `10^-6`, which is how the
paper reaches it; this needs an upper bound on `log T0`: `log T0 < 22`. -/
theorem log_T0_lt : Real.log T0 < 22 := by
  rw [Real.log_lt_iff_lt_exp (by unfold T0; norm_num)]
  have he : Real.exp 22 = Real.exp 1 ^ 22 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h := Real.exp_one_gt_d9
  rw [he]; unfold T0
  calc (3.29e9 : ℝ) < 2.7182818283 ^ 22 := by norm_num
    _ ≤ Real.exp 1 ^ 22 := by gcongr

theorem S0_error_with_330 :
    330 * Real.log T0 / (3 * T0) + 2.01 * Real.sqrt (K / 8.7e36) * NT0 * 1 < (1e-6 : ℝ) := by
  have hT := log_T0_lt
  have hs : Real.sqrt (K / 8.7e36) < 1.08e-17 := by
    rw [Real.sqrt_lt' (by norm_num)]; unfold K; norm_num
  have hT0 : (0 : ℝ) < Real.log T0 := by linarith [log_T0_gt]
  have h1 : 330 * Real.log T0 / (3 * T0) < 330 * 22 / (3 * T0) := by
    apply div_lt_div_of_pos_right _ (by unfold T0; norm_num); nlinarith
  have h3 : (330 : ℝ) * 22 / (3 * T0) < 7.36e-7 := by unfold T0; norm_num
  unfold NT0; nlinarith [Real.sqrt_nonneg (K / 8.7e36)]

/-- `A₁` error, the analogous step for `S_{η₁,1}(x, α)` with `c₁ = 0.1`: under `10^-6`.
MATCHES the paper. -/
theorem S1_error_ok :
    229.2 * Real.log T0 / (3 * T0) + 2.01 * Real.sqrt 10 * Real.sqrt (1 / 8.7e36) * NT0 *
      (7 / 10) < (1e-6 : ℝ) := by
  have hT := log_T0_lt
  have hT0 : (0 : ℝ) < Real.log T0 := by linarith [log_T0_gt]
  have hs1 : Real.sqrt 10 < 3.17 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2 : Real.sqrt (1 / 8.7e36) < 3.4e-19 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h1 : 229.2 * Real.log T0 / (3 * T0) < 229.2 * 22 / (3 * T0) := by
    apply div_lt_div_of_pos_right _ (by unfold T0; norm_num); nlinarith
  have h3 : (229.2 : ℝ) * 22 / (3 * T0) < 5.11e-7 := by unfold T0; norm_num
  have hp : 2.01 * Real.sqrt 10 * Real.sqrt (1 / 8.7e36) < 2.01 * 3.17 * 3.4e-19 := by
    have := Real.sqrt_nonneg 10; have := Real.sqrt_nonneg (1 / 8.7e36)
    have : Real.sqrt 10 * Real.sqrt (1 / 8.7e36) < 3.17 * 3.4e-19 := by nlinarith
    linarith
  unfold NT0; nlinarith

/-- (8.13): the mean value theorem error `N0 T0 / (5.4 x)` is below `10^-10` for
`x ≥ 8.7 · 10^36`. MATCHES, with room. -/
theorem D_error_ok {x : ℝ} (hx : 8.7e36 ≤ x) : N0 * T0 / (5.4 * x) ≤ 1e-10 := by
  have hx0 : 0 < x := by linarith
  rw [div_le_iff₀ (by positivity)]; unfold N0 T0; nlinarith

/-- FINDING: the printed bound for (8.15),
`10^-6 x √(T0/3.6π) (2/(1 - log(2T0/3.6π)/log x) · 4 log 2 · 1.04)^{1/2}`, is more than
`0.04 x` for every `x` with `0 ≤ r < 1`, `r = log(2T0/3.6π)/log x`; the paper says it can
be bounded by `0.02 x`. The main result survives; see FINDINGS.md. -/
theorem eq815_exceeds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (0.04 : ℝ) < 1e-6 * Real.sqrt (T0 / (3.6 * Real.pi)) *
      Real.sqrt (2 / (1 - r) * (4 * Real.log 2) * 1.04) := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have h2 := Real.log_two_gt_d9
  have hA : (2.9e8 : ℝ) < T0 / (3.6 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]; unfold T0; nlinarith
  have hB : (5.76 : ℝ) < 2 / (1 - r) * (4 * Real.log 2) * 1.04 := by
    have h1r : 2 ≤ 2 / (1 - r) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    nlinarith
  have hsA : (17000 : ℝ) < Real.sqrt (T0 / (3.6 * Real.pi)) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  have hsB : (2.4 : ℝ) < Real.sqrt (2 / (1 - r) * (4 * Real.log 2) * 1.04) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  nlinarith

end LeanLab.Tao2012.Numerics

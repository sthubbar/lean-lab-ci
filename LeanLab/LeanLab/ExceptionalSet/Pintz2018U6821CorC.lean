/-
P0016 Pintz 2018, arXiv 1804.09084v2, unit U-6821, CLOUD 20261021T0316Z-cloud57, T2.
Corollary 1 of Theorem C, p. 13, and the tail term of (9.6), p. 39.

Part 1, Corollary 1 reproduced. Theorem C, (4.3) to (4.5) on the rendered p. 12, bounds the
weighted zero sum by `C₂ = C₁ √(B_{φ,κ}(Λ) B_{φ,r}(Λ)) / κ`, `C₁ = (2φ+2c₁+c₂)/(2c₁c₂)`,
`B_{φ,ω}(y) = (φ/2)(1-e^{-2ωy})/y + ((1-e^{-ωy})/y)²`. Display (4.1) prints
`r = (φ+c₁+c₂)/3`, but the proof, (5.3) and (5.4) on p. 20, sets `r = φ+c₁+c₂`, and only that
value gives the coefficient `(r+κ)/2 = 5/12` of (4.8). With `r = φ+c₁+c₂ = 2/3`, `φ = 1/3`,
`c₁ = 1/12`, `c₂ = 1/4`, `κ = 1/6`, `C₁ = 26`, the printed `E₀ = 22.281`, `E₁ = 15.6`,
`E₂ = 10.4` follow: `C₂(1.311) = 22.28087`, `C₂(2.421) = 15.59598`, `C₂(3.96) = 10.38272`,
proved below as `E0_reproduced`, `E1_reproduced`, `E2_reproduced`. The fourth value does not:
`C₂(5.8) = 7.07944 > 7.01 = E₃`, `E3_exceeds`. Corollary 1 states (4.8), (4.9) only for
`i = 0, 1, 2`, yet Section 9 p. 38 uses `E₃` from `Λ₃ = 5.8` in Lemma 6 Case 4. The effect is
below `10⁻⁵` on `c₄*`, numerics/corC_U6821.out, so it does not matter for the exponent 0.72.
This is a QUESTION, a misprint candidate, not a FINDING.

Part 2, the tail of (9.6). `tail_of_weighted`: any weight `e^{-Wλ - σ d}`, `d = max(0, Λ₀-λ)`,
with `σ ≤ W ≤ A` gives `Σ e^{-A max(λ,Λ₀)} ≤ e^{-(A-W)Λ₀} Σ e^{-Wλ-σd}`, exactly Pintz's step
in (9.6) with `W = 2(x₀+κ)`, `σ = (r+κ)/2`. Re-optimising `c₁, c₂, κ` in Theorem C, with
`φ = 1/3` kept, numerics/corC_U6821.py, the minimiser of `e^{WΛ₀} C₂(Λ₀)` is independent of `A`,
near `c₁ = 0.0961`, `c₂ = 0.2354`, `κ = 0.1664`; the rational point `c₁ = 12/125`,
`c₂ = 47/200`, `κ = 1/6`, `W = 4069/1500`, gives `C₂ < 20.74` and the tail at `25/7` below
`6.73`, against Pintz's `22.281 e^{-19Λ₀/21} > 6.80`: a gain of only 1.1 percent.
`tail_new_params` is CONDITIONAL ON Theorem C (4.3) at these parameters with `(1+Cε) ≤ 1+10⁻⁵`,
as a hypothesis; `tail_new_params_vacuity` instantiates it.

Consequence, numerics only, LAB RECONSTRUCTION of U-6815: in the direct recomputation of
Cases 1 to 6 the optimised tail moves the floor from `A > 3.56320`, exponent `0.719354`, to
`A > 3.56043`, exponent `0.719135`. Pintz's Section 9 cannot go below about `0.719` with his own
inputs by re-tuning Theorem C. Nothing here is a new bound; Zhao 2025 arXiv 2511.05631 claims
`7/10`, a preprint. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Pintz2018.Section9

namespace LeanLab.ExceptionalSet.Pintz2018U6821CorC
open Real Finset

/-! ### Definitions, (4.4) and (4.5) with `r = φ + c₁ + c₂` as in (5.3) -/

/-- `B_{φ,ω}(y)` of (4.5). -/
noncomputable def Bf (φ ω y : ℝ) : ℝ :=
  φ / 2 * ((1 - exp (-(2 * ω * y))) / y) + ((1 - exp (-(ω * y))) / y) ^ 2

/-- `C₂(φ, κ, Λ)` of (4.3), with `C₁` of (4.4) and `r = φ + c₁ + c₂`. -/
noncomputable def C2f (φ c1 c2 κ y : ℝ) : ℝ :=
  (2 * φ + 2 * c1 + c2) / (2 * c1 * c2) * sqrt (Bf φ κ y * Bf φ (φ + c1 + c2) y) / κ

/-! ### Generic bounds -/

theorem Bf_le {φ ω y lo1 lo2 : ℝ} (hy : 0 < y) (hφ : 0 ≤ φ) (hω : 0 ≤ ω)
    (h1 : lo1 ≤ exp (-(2 * ω * y))) (h2 : lo2 ≤ exp (-(ω * y))) :
    Bf φ ω y ≤ φ / 2 * ((1 - lo1) / y) + ((1 - lo2) / y) ^ 2 := by
  unfold Bf
  have e2 : exp (-(ω * y)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have a : (1 - exp (-(2 * ω * y))) / y ≤ (1 - lo1) / y :=
    (div_le_div_iff_of_pos_right hy).mpr (by linarith)
  have b0 : 0 ≤ (1 - exp (-(ω * y))) / y := div_nonneg (by linarith) hy.le
  have b : (1 - exp (-(ω * y))) / y ≤ (1 - lo2) / y :=
    (div_le_div_iff_of_pos_right hy).mpr (by linarith)
  have h3 := pow_le_pow_left₀ b0 b 2
  have h4 := mul_le_mul_of_nonneg_left a (by positivity : (0 : ℝ) ≤ φ / 2)
  linarith

theorem Bf_ge {φ ω y hi1 hi2 : ℝ} (hy : 0 < y) (hφ : 0 ≤ φ)
    (h1 : exp (-(2 * ω * y)) ≤ hi1) (h2 : exp (-(ω * y)) ≤ hi2) (hhi : hi2 ≤ 1) :
    φ / 2 * ((1 - hi1) / y) + ((1 - hi2) / y) ^ 2 ≤ Bf φ ω y := by
  unfold Bf
  have a : (1 - hi1) / y ≤ (1 - exp (-(2 * ω * y))) / y :=
    (div_le_div_iff_of_pos_right hy).mpr (by linarith)
  have b0 : 0 ≤ (1 - hi2) / y := div_nonneg (by linarith) hy.le
  have b : (1 - hi2) / y ≤ (1 - exp (-(ω * y))) / y :=
    (div_le_div_iff_of_pos_right hy).mpr (by linarith)
  have h3 := pow_le_pow_left₀ b0 b 2
  have h4 := mul_le_mul_of_nonneg_left a (by positivity : (0 : ℝ) ≤ φ / 2)
  linarith

theorem Bf_nonneg {φ ω y : ℝ} (hy : 0 < y) (hφ : 0 ≤ φ) (hω : 0 ≤ ω) : 0 ≤ Bf φ ω y := by
  have h := Bf_ge (φ := φ) (ω := ω) (hi1 := 1) (hi2 := 1) hy hφ
    (exp_le_one_iff.mpr (by nlinarith)) (exp_le_one_iff.mpr (by nlinarith)) le_rfl
  simpa using h

theorem C2f_lt {φ c1 c2 κ y b1 b2 E : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hκ : 0 < κ)
    (hφ : 0 ≤ φ) (hB1 : Bf φ κ y ≤ b1) (hB2 : Bf φ (φ + c1 + c2) y ≤ b2)
    (hB1n : 0 ≤ Bf φ κ y) (hB2n : 0 ≤ Bf φ (φ + c1 + c2) y) (hE : 0 < E)
    (hprod : b1 * b2 < (E * κ / ((2 * φ + 2 * c1 + c2) / (2 * c1 * c2))) ^ 2) :
    C2f φ c1 c2 κ y < E := by
  unfold C2f
  set C1 := (2 * φ + 2 * c1 + c2) / (2 * c1 * c2) with hC1
  have hC1p : 0 < C1 := by rw [hC1]; positivity
  have hs1 : sqrt (Bf φ κ y * Bf φ (φ + c1 + c2) y) ≤ sqrt (b1 * b2) :=
    sqrt_le_sqrt (mul_le_mul hB1 hB2 hB2n (le_trans hB1n hB1))
  have hs2 : sqrt (b1 * b2) < E * κ / C1 := (sqrt_lt' (by positivity)).mpr hprod
  have h3 : C1 * sqrt (Bf φ κ y * Bf φ (φ + c1 + c2) y) < C1 * (E * κ / C1) :=
    mul_lt_mul_of_pos_left (lt_of_le_of_lt hs1 hs2) hC1p
  have h4 : C1 * (E * κ / C1) = E * κ := by field_simp
  rw [div_lt_iff₀ hκ]
  linarith

theorem C2f_ge {φ c1 c2 κ y b1 b2 E : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hκ : 0 < κ)
    (hφ : 0 ≤ φ) (hB1 : b1 ≤ Bf φ κ y) (hB2 : b2 ≤ Bf φ (φ + c1 + c2) y)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hE : 0 ≤ E)
    (hprod : (E * κ / ((2 * φ + 2 * c1 + c2) / (2 * c1 * c2))) ^ 2 ≤ b1 * b2) :
    E ≤ C2f φ c1 c2 κ y := by
  unfold C2f
  set C1 := (2 * φ + 2 * c1 + c2) / (2 * c1 * c2) with hC1
  have hC1p : 0 < C1 := by rw [hC1]; positivity
  have hs1 : sqrt (b1 * b2) ≤ sqrt (Bf φ κ y * Bf φ (φ + c1 + c2) y) :=
    sqrt_le_sqrt (mul_le_mul hB1 hB2 hb2 (le_trans hb1 hB1))
  have hs2 : E * κ / C1 ≤ sqrt (b1 * b2) := by
    rw [show E * κ / C1 = sqrt ((E * κ / C1) ^ 2) from (sqrt_sq (by positivity)).symm]
    exact sqrt_le_sqrt hprod
  have h3 : C1 * (E * κ / C1) ≤ C1 * sqrt (Bf φ κ y * Bf φ (φ + c1 + c2) y) :=
    mul_le_mul_of_nonneg_left (le_trans hs2 hs1) hC1p.le
  have h4 : C1 * (E * κ / C1) = E * κ := by field_simp
  rw [le_div_iff₀ hκ]
  linarith

theorem lo_of {x q lo : ℝ} (hx : x = q) (h : lo ≤ exp (-q)) : lo ≤ exp (-x) := hx ▸ h
theorem hi_of {x q hi : ℝ} (hx : x = q) (h : exp (-q) ≤ hi) : exp (-x) ≤ hi := hx ▸ h

/-! ### Numerical exponential bounds, from `expneg_lower` and `expneg_upper` of Pintz2018 -/

section expbounds
open LeanLab.Pintz2018

macro "exp_lo" x:term : tactic => `(tactic| (
  have h1 := expneg_lower $x (by norm_num) (by norm_num)
  simp only [T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith))

macro "exp_hi" x:term : tactic => `(tactic| (
  have h1 := expneg_upper $x (by norm_num)
  simp only [T15, sum_range_succ, sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith))

theorem lo_a : (0.6459714314 : ℝ) ≤ exp (-(437 / 1000)) := by exp_lo (437 / 1000)
theorem lo_b : (0.8037234794 : ℝ) ≤ exp (-(437 / 2000)) := by exp_lo (437 / 2000)
theorem lo_c : (0.1741218391 : ℝ) ≤ exp (-(437 / 250)) := by exp_lo (437 / 250)
theorem lo_d : (0.4172790901 : ℝ) ≤ exp (-(437 / 500)) := by exp_lo (437 / 500)
theorem lo_e : (0.4461946442 : ℝ) ≤ exp (-(807 / 1000)) := by exp_lo (807 / 1000)
theorem lo_f : (0.6679780267 : ℝ) ≤ exp (-(807 / 2000)) := by exp_lo (807 / 2000)
theorem lo_g : (0.03963669295 : ℝ) ≤ exp (-(807 / 250)) := by exp_lo (807 / 250)
theorem lo_h : (0.1990896605 : ℝ) ≤ exp (-(807 / 500)) := by exp_lo (807 / 500)
theorem lo_i : (0.2671353019 : ℝ) ≤ exp (-(33 / 25)) := by exp_lo (33 / 25)
theorem lo_j : (0.5168513344 : ℝ) ≤ exp (-(33 / 50)) := by exp_lo (33 / 50)
theorem lo_k : (0.005092430792 : ℝ) ≤ exp (-(132 / 25)) := by exp_lo (132 / 25)
theorem lo_l : (0.07136126955 : ℝ) ≤ exp (-(66 / 25)) := by exp_lo (66 / 25)
theorem lo_m : (0.1751903818 : ℝ) ≤ exp (-(870941 / 500000)) := by exp_lo (870941 / 500000)
theorem lo_n : (0.4185575012 : ℝ) ≤ exp (-(870941 / 1000000)) := by exp_lo (870941 / 1000000)
theorem lo_p : (0.3053969548 : ℝ) ≤ exp (-(8303 / 7000)) := by exp_lo (8303 / 7000)

theorem hi_a : exp (-(437 / 1000)) ≤ (0.6459714315 : ℝ) := by exp_hi (437 / 1000)
theorem hi_b : exp (-(437 / 2000)) ≤ (0.8037234795 : ℝ) := by exp_hi (437 / 2000)
theorem hi_m : exp (-(870941 / 500000)) ≤ (0.1751903819 : ℝ) := by exp_hi (870941 / 500000)
theorem hi_n : exp (-(870941 / 1000000)) ≤ (0.4185575013 : ℝ) := by exp_hi (870941 / 1000000)
theorem hi_q : exp (-(29 / 15)) ≤ (0.1446651767 : ℝ) := by exp_hi (29 / 15)
theorem hi_r : exp (-(29 / 30)) ≤ (0.3803487566 : ℝ) := by exp_hi (29 / 30)
theorem hi_s : exp (-(116 / 15)) ≤ (0.0004379818 : ℝ) := by exp_hi (116 / 15)
theorem hi_t : exp (-(58 / 15)) ≤ (0.02092801334 : ℝ) := by exp_hi (58 / 15)
theorem hi_u : exp (-(3940429 / 3500000)) ≤ (0.3243808933 : ℝ) := by exp_hi (3940429 / 3500000)

end expbounds

/-! ### Part 1: Corollary 1 constants -/

/-- `E₀`: `C₂(1/3, 1/12, 1/4, 1/6; 1.311) < 22.281`, numerically `22.28087`. -/
theorem E0_reproduced : C2f (1 / 3) (1 / 12) (1 / 4) (1 / 6) 1.311 < 22.281 :=
  C2f_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Bf_le (by norm_num) (by norm_num) (by norm_num) (lo_of (by norm_num) lo_a) (lo_of (by norm_num) lo_b))
    (Bf_le (by norm_num) (by norm_num) (by norm_num) (lo_of (by norm_num) lo_c) (lo_of (by norm_num) lo_d))
    (Bf_nonneg (by norm_num) (by norm_num) (by norm_num))
    (Bf_nonneg (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

/-- `E₁`: `C₂(…; 2.421) < 15.6`, numerically `15.59598`. -/
theorem E1_reproduced : C2f (1 / 3) (1 / 12) (1 / 4) (1 / 6) 2.421 < 15.6 :=
  C2f_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Bf_le (by norm_num) (by norm_num) (by norm_num) (lo_of (by norm_num) lo_e) (lo_of (by norm_num) lo_f))
    (Bf_le (by norm_num) (by norm_num) (by norm_num) (lo_of (by norm_num) lo_g) (lo_of (by norm_num) lo_h))
    (Bf_nonneg (by norm_num) (by norm_num) (by norm_num))
    (Bf_nonneg (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

/-- `E₂`: `C₂(…; 3.96) < 10.4`, numerically `10.38272`. -/
theorem E2_reproduced : C2f (1 / 3) (1 / 12) (1 / 4) (1 / 6) 3.96 < 10.4 :=
  C2f_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Bf_le (by norm_num) (by norm_num) (by norm_num) (lo_of (by norm_num) lo_i) (lo_of (by norm_num) lo_j))
    (Bf_le (by norm_num) (by norm_num) (by norm_num) (lo_of (by norm_num) lo_k) (lo_of (by norm_num) lo_l))
    (Bf_nonneg (by norm_num) (by norm_num) (by norm_num))
    (Bf_nonneg (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

/-- `E₃`: `C₂(…; 5.8) ≥ 7.07 > 7.01`, numerically `7.07944`: Theorem C at `Λ₃ = 5.8` does not
give the printed `E₃ = 7.01`. A QUESTION about a misprint; immaterial for `0.72`. -/
theorem E3_exceeds : (7.01 : ℝ) < C2f (1 / 3) (1 / 12) (1 / 4) (1 / 6) 5.8 := by
  have h : (7.07 : ℝ) ≤ C2f (1 / 3) (1 / 12) (1 / 4) (1 / 6) 5.8 :=
    C2f_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Bf_ge (by norm_num) (by norm_num) (hi_of (by norm_num) hi_q) (hi_of (by norm_num) hi_r) (by norm_num))
      (Bf_ge (by norm_num) (by norm_num) (hi_of (by norm_num) hi_s) (hi_of (by norm_num) hi_t) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-! ### Part 2: the tail of (9.6) -/

/-- Pintz's step in (9.6), for any weight with `σ ≤ W ≤ A`. -/
theorem tail_of_weighted {ι : Type*} (s : Finset ι) (lam : ι → ℝ) {A W σ Λ0 K : ℝ}
    (hσW : σ ≤ W) (hWA : W ≤ A)
    (hC : ∑ j ∈ s, exp (-(W * lam j) - σ * max 0 (Λ0 - lam j)) ≤ K) :
    ∑ j ∈ s, exp (-(A * max (lam j) Λ0)) ≤ exp (-((A - W) * Λ0)) * K := by
  calc ∑ j ∈ s, exp (-(A * max (lam j) Λ0))
      ≤ ∑ j ∈ s, exp (-((A - W) * Λ0)) * exp (-(W * lam j) - σ * max 0 (Λ0 - lam j)) := by
        apply sum_le_sum
        intro j _
        rw [← exp_add]
        apply exp_le_exp.mpr
        rcases le_total Λ0 (lam j) with h | h
        · rw [max_eq_left h, max_eq_left (by linarith : Λ0 - lam j ≤ 0)]
          nlinarith [mul_nonneg (sub_nonneg.2 hWA) (sub_nonneg.2 h)]
        · rw [max_eq_right h, max_eq_right (by linarith : 0 ≤ Λ0 - lam j)]
          nlinarith [mul_nonneg (sub_nonneg.2 hσW) (sub_nonneg.2 h)]
    _ = exp (-((A - W) * Λ0)) * ∑ j ∈ s, exp (-(W * lam j) - σ * max 0 (Λ0 - lam j)) := by
        rw [mul_sum]
    _ ≤ exp (-((A - W) * Λ0)) * K := mul_le_mul_of_nonneg_left hC (exp_pos _).le

/-- Re-optimised Theorem C constant at `Λ₀`: `c₁ = 12/125`, `c₂ = 47/200`, `κ = 1/6`,
`C₂ < 20.74`, numerically `20.73741`, against `22.28087` for Pintz's choice. -/
theorem C2_new_lt : C2f (1 / 3) (12 / 125) (47 / 200) (1 / 6) 1.311 < 20.74 :=
  C2f_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Bf_le (by norm_num) (by norm_num) (by norm_num) (lo_of (by norm_num) lo_a) (lo_of (by norm_num) lo_b))
    (Bf_le (by norm_num) (by norm_num) (by norm_num) (lo_of (by norm_num) lo_m) (lo_of (by norm_num) lo_n))
    (Bf_nonneg (by norm_num) (by norm_num) (by norm_num))
    (Bf_nonneg (by norm_num) (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

theorem C2_new_ge : (20.73 : ℝ) ≤ C2f (1 / 3) (12 / 125) (47 / 200) (1 / 6) 1.311 :=
  C2f_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Bf_ge (by norm_num) (by norm_num) (hi_of (by norm_num) hi_a) (hi_of (by norm_num) hi_b) (by norm_num))
    (Bf_ge (by norm_num) (by norm_num) (hi_of (by norm_num) hi_m) (hi_of (by norm_num) hi_n) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The weight `W = 2(x₀+κ)`, `x₀ = 2φ+3c₁+c₂`, at the new parameters. -/
theorem W_new : (2 * (2 * (1 / 3) + 3 * (12 / 125) + 47 / 200 + 1 / 6) : ℝ) = 4069 / 1500 := by
  norm_num

/-- Tail of (9.6) at every weight `A ≥ W = 4069/1500`, CONDITIONAL ON Theorem C (4.3) at
`φ = 1/3, c₁ = 12/125, c₂ = 47/200, κ = 1/6, Λ = Λ₀ = 1.311` with `1 + Cε ≤ 1 + δ`. -/
theorem tail_new_params_gen {ι : Type*} (s : Finset ι) (lam : ι → ℝ) {A δ : ℝ}
    (hA : (4069 / 1500 : ℝ) ≤ A) (hδ0 : 0 ≤ δ)
    (hC : ∑ j ∈ s, exp (-(2 * (2 * (1 / 3) + 3 * (12 / 125) + 47 / 200 + 1 / 6) * lam j)
        - ((1 / 3 + 12 / 125 + 47 / 200) + 1 / 6) / 2 * max 0 (1.311 - lam j))
      ≤ (1 + δ) * C2f (1 / 3) (12 / 125) (47 / 200) (1 / 6) 1.311) :
    ∑ j ∈ s, exp (-(A * max (lam j) 1.311))
      ≤ exp (-((A - 4069 / 1500) * 1.311)) * ((1 + δ) * 20.74) := by
  have h := tail_of_weighted s lam (A := A) (by norm_num) (by rw [W_new]; exact hA) hC
  rw [W_new] at h
  have hK : (1 + δ) * C2f (1 / 3) (12 / 125) (47 / 200) (1 / 6) 1.311 ≤ (1 + δ) * 20.74 :=
    mul_le_mul_of_nonneg_left C2_new_lt.le (by linarith)
  exact le_trans h (mul_le_mul_of_nonneg_left hK (exp_pos _).le)

/-- At `A = 25/7`: tail `< 6.73`, CONDITIONAL ON Theorem C as in `tail_new_params_gen`,
`δ ≤ 10⁻⁵`. -/
theorem tail_new_params {ι : Type*} (s : Finset ι) (lam : ι → ℝ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100000)
    (hC : ∑ j ∈ s, exp (-(2 * (2 * (1 / 3) + 3 * (12 / 125) + 47 / 200 + 1 / 6) * lam j)
        - ((1 / 3 + 12 / 125 + 47 / 200) + 1 / 6) / 2 * max 0 (1.311 - lam j))
      ≤ (1 + δ) * C2f (1 / 3) (12 / 125) (47 / 200) (1 / 6) 1.311) :
    ∑ j ∈ s, exp (-(25 / 7 * max (lam j) 1.311)) < 6.73 := by
  have h := tail_new_params_gen s lam (A := 25 / 7) (by norm_num) hδ0 hC
  have he : exp (-((25 / 7 - 4069 / 1500) * 1.311 : ℝ)) ≤ 0.3243808933 :=
    hi_of (by norm_num) hi_u
  have h2 : exp (-((25 / 7 - 4069 / 1500) * 1.311 : ℝ)) * ((1 + δ) * 20.74)
      ≤ 0.3243808933 * ((1 + δ) * 20.74) :=
    mul_le_mul_of_nonneg_right he (by positivity)
  nlinarith

/-- Pintz's printed tail in (9.6) is above `6.80`: `22.281 e^{-19Λ₀/21} > 6.80`. -/
theorem pintz_tail_gt : (6.80 : ℝ) < 22.281 * exp (-(19 / 21 * 1.311)) := by
  have he : (0.3053969548 : ℝ) ≤ exp (-(19 / 21 * 1.311)) := lo_of (by norm_num) lo_p
  nlinarith

/-- Vacuity instance: one zero at `λ = 2`, `δ = 0`; the Theorem C hypothesis holds because
`C₂ ≥ 20.73`. -/
theorem tail_new_params_vacuity :
    ∑ j ∈ ({()} : Finset Unit), exp (-(25 / 7 * max ((fun _ => (2 : ℝ)) j) 1.311)) < 6.73 := by
  refine tail_new_params _ _ (δ := 0) le_rfl (by norm_num) ?_
  rw [sum_singleton]
  have h1 : exp (-(2 * (2 * (1 / 3) + 3 * (12 / 125) + 47 / 200 + 1 / 6) * (2 : ℝ))
      - ((1 / 3 + 12 / 125 + 47 / 200) + 1 / 6) / 2 * max 0 (1.311 - 2)) ≤ 1 :=
    exp_le_one_iff.mpr (by norm_num)
  have h2 := C2_new_ge
  linarith

end LeanLab.ExceptionalSet.Pintz2018U6821CorC

#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.E0_reproduced
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.E1_reproduced
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.E2_reproduced
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.E3_exceeds
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.tail_of_weighted
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.C2_new_lt
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.C2_new_ge
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.tail_new_params_gen
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.tail_new_params
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.pintz_tail_gt
#print axioms LeanLab.ExceptionalSet.Pintz2018U6821CorC.tail_new_params_vacuity

/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6402, track T2: a scripted port by gen/port32708_U6402.py of the U-6400 32.713 file to log log X₂ = 32.708, δ = 1.47716, ε₀ = 2.72·10⁻⁴, m(X₃) ≤ 1.33·10⁻⁹, α = 1/160000; the case (b) margin is asked only for 10⁻⁶ + 10⁻¹², enough for a positive Chen count. The 32.713 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6400, track T2: a scripted port by gen/port32713_U6400.py of the 32.716 file of PC U-1045 to log log X₂ = 32.708, δ = 1.47716, ε₀ = 2.72·10⁻⁴, m(X₃) ≤ 1.33·10⁻⁹ and α = 1/160000 of Section9A160.lean; numeric lemmas retightened where the build required, listed in the script. The ported header follows.
AI-written Lean code, Claude, 2026-10-19, CLOUD-built run 20261019T0903Z-22821 of the PC lab, unit U-1045, track T2, a scripted port of BJSm3272.lean of PC run 20261019T0703Z-249, U-1041, to log log X₂ = 32.708, δ = 1.47716, ε₀ = 2.72·10⁻⁴, m(X₃) ≤ 1.33·10⁻⁹; numeric lemmas retightened where the build required. The ported header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-19, PC run 20261019T0703Z-249, unit U-1041, ported from the cloud's BJSm3273.lean of U-5042, track T2.
P0009 BJS 2022, Lemma 32's `m(X₃)` at the lab's corrected Section 9 parameters moved to
`log log X₂ = 32.708`, `δ = 1.47716`, `X₃ = X₂^{1/8}`: BJSmX3.lean, run 20261018T0704Z-6940, with the
constants changed and the numeric lemmas retightened. The input `m(X₃) ≤ 1.33·10⁻⁹` of
At32708.margin_bP and margin_aP.

Notation as in BJSmX3: `Λ₃ = e^{32.708}/8`, `ℓ = Λ₃ - 15 log Λ₃`, `K = ℓ^δ`, `ν` of (91), `β₀ = 1 - ν`.
PROVED: `phi_le`, `φ(Y) ≤ 33.7·10⁻¹²` for every `Y ≥ ℓ`; `m_le`, `m(X₃) ≤ 1.33·10⁻⁹` for any `v` in
`[0, 33.7·10⁻¹²]`. Python, mpmath at 40 digits, CLOUD 20261020T1217Z-cloud42: `ν ℓ = 146.6398`, `v ≈ 3.3295·10⁻¹¹`,
`m ≈ 1.3043·10⁻⁹`, at log log X₂ = 32.708, δ = 1.47716. The heart is `ν ℓ ≥ 146.63` against `4 log ℓ ≈ 122.514`.
Chen's theorem is not in doubt; Goldbach is open.
-/
import Mathlib

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJSm32708

/-- `log X₃ = e^{32.708}/8`. -/
def Λ3 : ℝ := exp (32708 / 1000) / 8
/-- `log x₂(X₃)`. -/
def ℓ : ℝ := Λ3 - 15 * log Λ3
/-- `K_δ(x₂) = log^δ x₂`, `δ = 1.47716`. -/
def K : ℝ := ℓ ^ (1.47716 : ℝ)
/-- `ν(x₂)`, (91), `R₁ = 2.0452`. -/
def ν : ℝ := min (100 / (sqrt K * log K ^ 2)) (1 / (2 * 2.0452 * (10 * log ℓ)))
/-- `β₀(x₂) = 1 - ν(x₂)`. -/
def β0 : ℝ := 1 - ν

/-- the bracket of (72) at `Y = log y`. -/
def φ (Y : ℝ) : ℝ :=
  3.2e-8 / Y ^ 4 + Y ^ 4 * (exp ((β0 - 1) * Y) / β0 + 1.02 * Y ^ 10 / exp (Y / 2) +
    3 * Y ^ 10 / exp (2 * Y / 3))

/-- `v₀(X₃)` of Lemma 29, (71), with `v'₀ ≤ v`. -/
def v0 (v : ℝ) : ℝ := v * (1 + 1 / (Λ3 ^ 10 * ℓ ^ 5) + 1 / ((1 - 6 / ℓ) * Λ3)) + 3 / Λ3

/-- `m(X₃)`, Lemma 32. -/
def mX3 (v : ℝ) : ℝ :=
  39 * v0 v + 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) + 26 * Λ3 ^ 5 / ℓ ^ 10 +
    88 * Λ3 ^ 5 * (exp (-(8 / 3 * Λ3)) + exp (-(Λ3 / 2))) + 106 / Λ3 ^ 6

lemma exp_nat_ge (n : ℕ) : 2.7182818283 ^ n ≤ exp (n : ℝ) := by
  rw [← exp_one_pow]; exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le n

lemma exp32708_ge : (1.5 * 10 ^ 14 : ℝ) ≤ exp (32708 / 1000) := by
  have e : exp (32708 / 1000 : ℝ) = exp 1 ^ 32 * exp (708 / 1000) := by
    rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 32 ≤ exp 1 ^ 32 :=
    pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 32
  have h2 : (1.95 : ℝ) ≤ exp (708 / 1000) := by
    have := quadratic_le_exp_of_nonneg (x := (708 / 1000 : ℝ)) (by norm_num); norm_num at this ⊢; linarith
  rw [e]
  have h3 := mul_le_mul h1 h2 (by norm_num) (by positivity)
  have h4 : (1.5 * 10 ^ 14 : ℝ) ≤ (2.7182818283 : ℝ) ^ 32 * 1.95 := by norm_num
  linarith

lemma Λ3_ge : (10 ^ 13 : ℝ) ≤ Λ3 := by unfold Λ3; have := exp32708_ge; linarith

lemma log_Λ3 : log Λ3 = 32708 / 1000 - 3 * log 2 := by
  unfold Λ3
  rw [log_div (exp_pos _).ne' (by norm_num), log_exp, show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
  push_cast; ring

lemma ℓ_bounds : Λ3 * (1 - 1 / 10 ^ 10) ≤ ℓ ∧ ℓ ≤ Λ3 := by
  unfold ℓ
  have h := Λ3_ge
  have hl := log_Λ3
  have l2 := log_two_gt_d9
  have l2' := log_two_lt_d9
  constructor <;> rw [hl] <;> norm_num at l2 l2' ⊢ <;> nlinarith

lemma ℓ_pos : 0 < ℓ := by have := ℓ_bounds; have := Λ3_ge; nlinarith

/-- `30.6285 ≤ log ℓ ≤ 30.6286`. -/
lemma logℓ_bounds : 30.6285 ≤ log ℓ ∧ log ℓ ≤ 30.6286 := by
  obtain ⟨h1, h2⟩ := ℓ_bounds
  have hΛ := Λ3_ge
  have hl := log_Λ3
  have l2 := log_two_gt_d9
  have l2' := log_two_lt_d9
  constructor
  · have : log (Λ3 * (1 - 1 / 10 ^ 10)) ≤ log ℓ := log_le_log (by positivity) h1
    rw [log_mul (by positivity) (by norm_num), hl] at this
    have h3 := Real.one_sub_inv_le_log_of_pos (x := (1 - 1 / 10 ^ 10 : ℝ)) (by norm_num)
    norm_num at l2' h3 this ⊢; linarith
  · have : log ℓ ≤ log Λ3 := log_le_log ℓ_pos h2
    rw [hl] at this; norm_num at l2 this ⊢; linarith

/-- **`ν ℓ ≥ 146.63`.** -/
lemma νℓ_ge : 146.63 ≤ ν * ℓ := by
  obtain ⟨u1, u2⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  set u := log ℓ with hu
  have hK : K = exp (u * 1.47716) := by unfold K; rw [rpow_def_of_pos hℓ]
  have hlogK : log K = 1.47716 * u := by rw [hK, log_exp]; ring
  have hsK : sqrt K = exp (0.73858 * u) := by
    rw [hK, sqrt_eq_rpow, ← exp_mul]; ring_nf
  have hℓe : ℓ = exp u := (exp_log hℓ).symm
  unfold ν
  rw [hsK, hlogK]
  -- first branch: 100 ℓ / (e^{0.73858 u} (1.47716 u)²) = 100 e^{0.26142 u}/(1.47716 u)²
  have br1 : 146.63 ≤ 100 / (exp (0.73858 * u) * (1.47716 * u) ^ 2) * ℓ := by
    rw [hℓe, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e : exp u = exp (0.73858 * u) * exp (0.26142 * u) := by rw [← exp_add]; ring_nf
    rw [e]
    have hE : 3001.6 ≤ exp (0.26142 * u) := by
      have e8 : exp (0.26142 * u) = exp ((8 : ℕ) : ℝ) * exp (0.26142 * u - 8) := by
        rw [← exp_add]; push_cast; ring_nf
      rw [e8]
      have a := exp_nat_ge 8
      have b := quadratic_le_exp_of_nonneg (x := 0.26142 * u - 8) (by nlinarith)
      have b' : 1.006925 ≤ exp (0.26142 * u - 8) := by nlinarith
      have := mul_le_mul a b' (by norm_num) (by positivity)
      have c : (3001.6 : ℝ) ≤ 2.7182818283 ^ 8 * 1.006925 := by norm_num
      linarith
    have hu2 : (1.47716 * u) ^ 2 ≤ 2046.97 := by nlinarith
    have hp := exp_pos (0.73858 * u)
    have : 146.63 * (exp (0.73858 * u) * (1.47716 * u) ^ 2) ≤ 146.63 * (exp (0.73858 * u) * 2046.97) := by
      gcongr
    nlinarith
  have br2 : 146.63 ≤ 1 / (2 * 2.0452 * (10 * u)) * ℓ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have := ℓ_bounds.1; have := Λ3_ge; nlinarith
  rcases min_choice (100 / (exp (0.73858 * u) * (1.47716 * u) ^ 2)) (1 / (2 * 2.0452 * (10 * u))) with h | h
  · rw [h]; exact br1
  · rw [h]; exact br2

lemma ν_pos : 0 < ν := by
  have := νℓ_ge; have := ℓ_pos; nlinarith

lemma ν_le : ν ≤ 1 / 1000 := by
  obtain ⟨u1, _⟩ := logℓ_bounds
  unfold ν
  refine (min_le_right _ _).trans ?_
  rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith

/-- `Y⁴ e^{-νY}` decreases for `Y ≥ ℓ`, since `ν ℓ ≥ 4`. -/
lemma decay (Y : ℝ) (hY : ℓ ≤ Y) : Y ^ 4 * exp (-ν * Y) ≤ ℓ ^ 4 * exp (-ν * ℓ) := by
  have hℓ := ℓ_pos
  have hν := νℓ_ge
  have hd : 0 ≤ Y - ℓ := by linarith
  have h1 : Y / ℓ ≤ exp ((Y - ℓ) / ℓ) := by
    have := add_one_le_exp ((Y - ℓ) / ℓ)
    have e : (Y - ℓ) / ℓ + 1 = Y / ℓ := by field_simp; ring
    linarith
  have h2 : (Y / ℓ) ^ 4 ≤ exp (4 * ((Y - ℓ) / ℓ)) := by
    have := pow_le_pow_left₀ (div_nonneg (by linarith) hℓ.le) h1 4
    rw [← exp_nat_mul] at this; push_cast at this; exact this
  have h3 : 4 * ((Y - ℓ) / ℓ) ≤ ν * (Y - ℓ) := by
    rw [← mul_div_assoc, div_le_iff₀ hℓ]; nlinarith
  have h4 : (Y / ℓ) ^ 4 ≤ exp (ν * (Y - ℓ)) := h2.trans (exp_le_exp.mpr h3)
  have e1 : Y ^ 4 = ℓ ^ 4 * (Y / ℓ) ^ 4 := by field_simp
  have e2 : exp (-ν * ℓ) = exp (ν * (Y - ℓ)) * exp (-ν * Y) := by rw [← exp_add]; ring_nf
  rw [e1, e2]
  have := exp_pos (-ν * Y)
  have : 0 ≤ ℓ ^ 4 := by positivity
  calc ℓ ^ 4 * (Y / ℓ) ^ 4 * exp (-ν * Y) ≤ ℓ ^ 4 * exp (ν * (Y - ℓ)) * exp (-ν * Y) := by
        gcongr
    _ = _ := by ring

lemma big_poly (Y : ℝ) (hY : 9 * 10 ^ 12 ≤ Y) : Y ^ 14 / exp (Y / 2) ≤ 1 / 10 ^ 40 := by
  have hE := pow_div_factorial_le_exp (x := Y / 2) (by positivity) 20
  have hf : ((Nat.factorial 20 : ℕ) : ℝ) ≤ 10 ^ 19 := by norm_num [Nat.factorial]
  have h20 : (Y / 2) ^ 20 / 10 ^ 19 ≤ exp (Y / 2) :=
    le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hf) hE
  rw [div_le_iff₀ (exp_pos _)]
  have hY6 : (10 : ℝ) ^ 40 * 2 ^ 20 * 10 ^ 19 ≤ Y ^ 6 := by
    have : (9 * 10 ^ 12 : ℝ) ^ 6 ≤ Y ^ 6 := pow_le_pow_left₀ (by norm_num) hY 6
    have c : (10 : ℝ) ^ 40 * 2 ^ 20 * 10 ^ 19 ≤ (9 * 10 ^ 12) ^ 6 := by norm_num
    linarith
  have hY14 : 0 ≤ Y ^ 14 := by positivity
  have key : Y ^ 14 * (10 ^ 40 * 2 ^ 20 * 10 ^ 19) ≤ Y ^ 14 * Y ^ 6 :=
    mul_le_mul_of_nonneg_left hY6 hY14
  have e : 1 / 10 ^ 40 * ((Y / 2) ^ 20 / 10 ^ 19) = Y ^ 14 * Y ^ 6 / (10 ^ 40 * 2 ^ 20 * 10 ^ 19) := by
    ring
  have : Y ^ 14 ≤ 1 / 10 ^ 40 * ((Y / 2) ^ 20 / 10 ^ 19) := by
    rw [e, le_div_iff₀ (by positivity)]; linarith
  have : 1 / 10 ^ 40 * ((Y / 2) ^ 20 / 10 ^ 19) ≤ 1 / 10 ^ 40 * exp (Y / 2) :=
    mul_le_mul_of_nonneg_left h20 (by norm_num)
  linarith

/-- **`φ(Y) ≤ 33.7·10⁻¹²` for every `Y ≥ log x₂(X₃)`, so `v'₀(X₃) ≤ 33.7·10⁻¹²`.** -/
theorem phi_le (Y : ℝ) (hY : ℓ ≤ Y) : φ Y ≤ 33.7 / 10 ^ 12 := by
  have hℓ := ℓ_pos
  have hℓ13 : (10 ^ 13 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓ := by
    have := ℓ_bounds.1; have := Λ3_ge; nlinarith
  have hY13 : (9 * 10 ^ 12 : ℝ) ≤ Y := by norm_num at hℓ13; linarith
  have hYp : 0 < Y := by linarith
  have hν1 := ν_le
  have hν0 := ν_pos
  have hb : 0.999 ≤ β0 := by unfold β0; norm_num at hν1 ⊢; linarith
  unfold φ
  -- term 1
  have t1 : 3.2e-8 / Y ^ 4 ≤ 1 / 10 ^ 50 := by
    rw [div_le_iff₀ (by positivity)]
    have : (9 * 10 ^ 12 : ℝ) ^ 4 ≤ Y ^ 4 := pow_le_pow_left₀ (by norm_num) hY13 4
    norm_num at this ⊢; nlinarith
  -- term 2, the Siegel zero term
  have e2 : (β0 - 1) * Y = -ν * Y := by unfold β0; ring
  rw [e2]
  have d := decay Y hY
  have hu := logℓ_bounds.2
  have hℓ4 : ℓ ^ 4 ≤ exp (4 * 30.6286) := by
    have : ℓ = exp (log ℓ) := (exp_log hℓ).symm
    rw [this, ← exp_nat_mul]; push_cast; exact exp_le_exp.mpr (by linarith)
  have hνℓ : exp (-ν * ℓ) ≤ exp (-146.63) := exp_le_exp.mpr (by have := νℓ_ge; nlinarith)
  have hcomb : ℓ ^ 4 * exp (-ν * ℓ) ≤ exp (4 * 30.6286) * exp (-146.63) :=
    mul_le_mul hℓ4 hνℓ (exp_pos _).le (exp_pos _).le
  have hx : exp (4 * 30.6286) * exp (-146.63) ≤ 33.64 / 10 ^ 12 := by
    rw [← exp_add]
    have e : (4 * 30.6286 + -146.63 : ℝ) = -((24 : ℕ) : ℝ) - 0.1156 := by norm_num
    rw [e, sub_eq_add_neg, exp_add, exp_neg]
    have a := exp_nat_ge 24
    have b : exp (-0.1156 : ℝ) ≤ 0.89084 := by
      have q := Real.sum_le_exp_of_nonneg (x := (0.1156 : ℝ)) (by norm_num) 7
      rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
      norm_num [Finset.sum_range_succ, Nat.factorial] at q ⊢; linarith
    have hp : 0 < exp ((24 : ℕ) : ℝ) := exp_pos _
    have c : (exp ((24 : ℕ) : ℝ))⁻¹ ≤ (2.7182818283 ^ 24)⁻¹ := by
      rw [inv_le_inv₀ hp (by positivity)]; exact a
    have : (exp ((24 : ℕ) : ℝ))⁻¹ * exp (-0.1156) ≤ (2.7182818283 ^ 24)⁻¹ * 0.89084 :=
      mul_le_mul c b (exp_pos _).le (by positivity)
    have h25 : ((2.7182818283 : ℝ) ^ 25)⁻¹ * 0.89084 ≤ 33.64 / 10 ^ 12 := by
      rw [inv_mul_le_iff₀ (by positivity)]; norm_num
    linarith
  have t2 : Y ^ 4 * (exp (-ν * Y) / β0) ≤ 33.68 / 10 ^ 12 := by
    have : Y ^ 4 * (exp (-ν * Y) / β0) = (Y ^ 4 * exp (-ν * Y)) / β0 := by ring
    rw [this, div_le_iff₀ (by linarith)]
    have : Y ^ 4 * exp (-ν * Y) ≤ 33.64 / 10 ^ 12 := by linarith
    nlinarith
  -- terms 3 and 4
  have t3 : Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) ≤ 1.02 / 10 ^ 40 := by
    have := big_poly Y (by linarith)
    have e : Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) = 1.02 * (Y ^ 14 / exp (Y / 2)) := by ring
    rw [e]; nlinarith
  have t4 : Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) ≤ 3 / 10 ^ 40 := by
    have h := big_poly Y (by linarith)
    have hle : exp (Y / 2) ≤ exp (2 * Y / 3) := exp_le_exp.mpr (by linarith)
    have : Y ^ 14 / exp (2 * Y / 3) ≤ Y ^ 14 / exp (Y / 2) :=
      div_le_div_of_nonneg_left (by positivity) (exp_pos _) hle
    have e : Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) = 3 * (Y ^ 14 / exp (2 * Y / 3)) := by ring
    rw [e]; nlinarith
  have e : Y ^ 4 * (exp (-ν * Y) / β0 + 1.02 * Y ^ 10 / exp (Y / 2) + 3 * Y ^ 10 / exp (2 * Y / 3)) =
      Y ^ 4 * (exp (-ν * Y) / β0) + Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) +
        Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) := by ring
  rw [e]
  norm_num at t1 t2 t3 t4 ⊢
  linarith

/-- **`m(X₃) ≤ 1.33·10⁻⁹`** for any `v` with `0 ≤ v ≤ 33.7·10⁻¹²`, the bound of `phi_le`. -/
theorem m_le (v : ℝ) (_hv0 : 0 ≤ v) (hv : v ≤ 33.7 / 10 ^ 12) : mX3 v ≤ 1330 / 10 ^ 12 := by
  have hΛ := Λ3_ge
  have hΛ' : (1.85 * 10 ^ 13 : ℝ) ≤ Λ3 := by unfold Λ3; have := exp32708_ge; linarith
  have hℓ13 : (10 ^ 13 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓ := by
    have := ℓ_bounds.1; nlinarith
  have hℓ := ℓ_pos
  unfold mX3 v0
  have a1 : 1 / (Λ3 ^ 10 * ℓ ^ 5) ≤ 1 / 10 ^ 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ Λ3 ^ 10 := one_le_pow₀ (by linarith)
    have : (10 ^ 12 : ℝ) ≤ ℓ ^ 5 := by
      have := pow_le_pow_left₀ (by norm_num) hℓ13 5; norm_num at this ⊢; linarith
    nlinarith
  have a2 : 1 / ((1 - 6 / ℓ) * Λ3) ≤ 1 / 10 ^ 12 := by
    have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; norm_num at hℓ13; linarith
    have h6p : 0 < 1 - 6 / ℓ := by linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have a3 : 3 / Λ3 ≤ 3 / (1.85 * 10 ^ 13) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ'
  have b1 : 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) ≤ 1 / 10 ^ 20 := by
    have hlog : 1 ≤ log Λ3 := by rw [log_Λ3]; have := log_two_lt_d9; norm_num at this ⊢; linarith
    have hE2 := pow_div_factorial_le_exp (x := Λ3) (by positivity) 20
    have hf : ((Nat.factorial 20 : ℕ) : ℝ) ≤ 10 ^ 19 := by norm_num [Nat.factorial]
    have h20 : Λ3 ^ 20 / 10 ^ 19 ≤ exp Λ3 :=
      le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hf) hE2
    rw [div_le_iff₀ (by have := exp_pos Λ3; positivity)]
    have hΛ4 : (10 ^ 52 : ℝ) ≤ Λ3 ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hΛ 4; norm_num at this ⊢; linarith
    have hΛ16 : 0 ≤ Λ3 ^ 16 := by positivity
    have : 108 * Λ3 ^ 16 ≤ 1 / 10 ^ 20 * (Λ3 ^ 20 / 10 ^ 19) := by
      have : Λ3 ^ 20 = Λ3 ^ 16 * Λ3 ^ 4 := by ring
      rw [this]; nlinarith [mul_le_mul_of_nonneg_left hΛ4 hΛ16]
    have : Λ3 ^ 20 / 10 ^ 19 ≤ exp Λ3 * log Λ3 := by
      have := exp_pos Λ3; nlinarith
    nlinarith
  have b2 : 26 * Λ3 ^ 5 / ℓ ^ 10 ≤ 1 / 10 ^ 20 := by
    have hℓΛ : Λ3 * (1 - 1 / 10 ^ 10) ≤ ℓ := ℓ_bounds.1
    have : (Λ3 / 2) ^ 10 ≤ ℓ ^ 10 := pow_le_pow_left₀ (by positivity) (by nlinarith) 10
    rw [div_le_iff₀ (by positivity)]
    have hΛ5 : (10 ^ 65 : ℝ) ≤ Λ3 ^ 5 := by
      have := pow_le_pow_left₀ (by norm_num) hΛ 5; norm_num at this ⊢; linarith
    have e : (Λ3 / 2) ^ 10 = Λ3 ^ 5 * Λ3 ^ 5 / 1024 := by ring
    rw [e] at this
    have h0 : 0 ≤ Λ3 ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hΛ5 h0]
  have b3 : 88 * Λ3 ^ 5 * (exp (-(8 / 3 * Λ3)) + exp (-(Λ3 / 2))) ≤ 1 / 10 ^ 20 := by
    have hE := big_poly Λ3 (by linarith)
    have h1 : exp (-(8 / 3 * Λ3)) ≤ exp (-(Λ3 / 2)) := exp_le_exp.mpr (by linarith)
    have h2 : Λ3 ^ 5 * exp (-(Λ3 / 2)) ≤ 1 / 10 ^ 40 := by
      rw [exp_neg, ← div_eq_mul_inv]
      have : Λ3 ^ 5 / exp (Λ3 / 2) ≤ Λ3 ^ 14 / exp (Λ3 / 2) := by
        apply div_le_div_of_nonneg_right _ (exp_pos _).le
        exact pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have h0 : 0 ≤ Λ3 ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_left h1 h0
    nlinarith
  have b4 : 106 / Λ3 ^ 6 ≤ 1 / 10 ^ 20 := by
    rw [div_le_iff₀ (by positivity)]
    have := pow_le_pow_left₀ (by norm_num) hΛ 6; norm_num at this ⊢; linarith
  have hv' : v * (1 + 1 / (Λ3 ^ 10 * ℓ ^ 5) + 1 / ((1 - 6 / ℓ) * Λ3)) ≤
      33.7 / 10 ^ 12 * (1 + 2 / 10 ^ 12) := by
    have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; norm_num at hℓ13; linarith
    have q1 : 0 ≤ 1 / (Λ3 ^ 10 * ℓ ^ 5) := by positivity
    have q2 : 0 ≤ 1 / ((1 - 6 / ℓ) * Λ3) :=
      div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
    apply mul_le_mul hv (by linarith) (by linarith) (by norm_num)
  norm_num at hv' a3 b1 b2 b3 b4 ⊢
  linarith

/-- v'₀(X₃), the max of (72) over y ≥ x₂(X₃), Y = log y. -/
def vS : ℝ := ⨆ Y : Set.Ici ℓ, φ Y

lemma phi_nonneg {Y : ℝ} (hY : ℓ ≤ Y) : 0 ≤ φ Y := by
  have hY0 : 0 < Y := ℓ_pos.trans_le hY
  have hb : 0 < β0 := by unfold β0; have := ν_le; linarith
  unfold φ
  positivity

lemma vS_bounds : 0 ≤ vS ∧ vS ≤ 33.7 / 10 ^ 12 := by
  have : Nonempty (Set.Ici ℓ) := ⟨⟨ℓ, Set.mem_Ici.mpr le_rfl⟩⟩
  have hb : BddAbove (Set.range fun Y : Set.Ici ℓ => φ Y) :=
    ⟨33.7 / 10 ^ 12, by rintro _ ⟨Y, rfl⟩; exact phi_le Y Y.2⟩
  exact ⟨(phi_nonneg le_rfl).trans (le_ciSup hb ⟨ℓ, Set.mem_Ici.mpr le_rfl⟩),
    ciSup_le fun Y => phi_le Y Y.2⟩

lemma mX3_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mX3 v := by
  have hΛ := Λ3_ge
  have hℓ := ℓ_pos
  have hℓ13 : (10 ^ 13 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓ := by
    have := ℓ_bounds.1; nlinarith
  have h6 : 6 / ℓ < 1 := by rw [div_lt_one hℓ]; norm_num at hℓ13; linarith
  have hq : 0 ≤ 1 / ((1 - 6 / ℓ) * Λ3) := by
    apply div_nonneg (by norm_num); apply mul_nonneg (by linarith) (by linarith)
  have hlog : 0 < log Λ3 := log_pos (by linarith)
  have hΛ0 : 0 < Λ3 := by linarith
  unfold mX3 v0
  set q := 1 / ((1 - 6 / ℓ) * Λ3)
  positivity

/-- **The input of At32708.margin_bP and margin_aP**: `0 ≤ m(X₃) ≤ 1.33·10⁻⁹` at log log X₂ = 32.708,
`δ = 1.47716`, with `v'₀(X₃)` the supremum `vS`. -/
theorem mX3_vS_bounds : 0 ≤ mX3 vS ∧ mX3 vS ≤ 1330 / 10 ^ 12 := by
  obtain ⟨v0, v1⟩ := vS_bounds
  exact ⟨mX3_nonneg v0, m_le _ v0 v1⟩

end LeanLab.ChenExplicit.BJSm32708

/-
AI-written Lean code, Claude, Lean Lab run 20261022T2003Z-18, unit U-1498, track T2 FRONTIER,
paper P0009 Bordignon, Johnston, Starichkova 2022, arXiv 2207.09452 v6, idea I-0105.

m of X3 at log log X2 = 31.567, X3 = X2^(1/8), delta2 = 1.50023, the U-1490 model value at the
model floor, with the plus-4 Siegel constant of U1490SiegelPlus.lean in the nu of x2 of X3.
Source, WebFetch of arxiv.org/pdf/2207.09452v6 this unit: x2(Y) = Y / log^15 Y and
K_delta(x) = log^delta x, Q1(x) = log^10 x in eqs (55), (56); nu(x2) = min(100/(sqrt K log^2 K),
1/(2 R1 log Q1(x2))), beta0(x2) = 1 - nu(x2), R1 = 2.0452 from Theorem 25; m(X3) = 39 v0(X3)
+ 108 log^16 X3/(X3 log log X3) + 26 log^5 X3/log^10 x2(X3) + 88 log^5 X3 (X3^(-8/3) + X3^(-1/2))
+ 106/log^6 X3.  The fetched v6 text labels these Lemma 31 and eq (71); the lab's older files
call them Lemma 32 and eq (91).  The bracket phi of v0 is the lab's BJSm32155.phi, unchanged.

The plus-4 nu: since 4 log K = 176.95 > 100 here, max(100, 4 log K)/(sqrt K log^2 K) equals
4/(sqrt K log K), so `νP = min(4/(sqrt K log K), 1/(2 R1 (10 log ℓ)))`.

PROVED: `νPℓ_ge`, νP ℓ >= 143.33, true value 143.338; `phi_le`, phi(Y) <= 9.54e-12 for Y >= ℓ;
`m_le`, `mX3_vS_bounds`, 0 <= m(X3) <= 3.95e-10, true value about 3.86e-10.
CONDITIONAL ON ClassNumberPlus4, MeanValueStep, BordignonEq9, BordignonThm13: `nuP3_siegel`,
every real zero of an even primitive real L(s, chi) mod q, 4e5 < q <= K, is at most 1 - νP.
NOT covered: odd characters and q <= 4e5 in the range of eq (71), as in U-1490.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ChenExplicit.U1490SiegelPlus

open Real

noncomputable section
namespace LeanLab.ChenExplicit.U1498MX3

/-- `log X₃ = e^{31.567}/8`. -/
def Λ3 : ℝ := exp (31567 / 1000) / 8
/-- `log x₂(X₃)`, eq (55). -/
def ℓ : ℝ := Λ3 - 15 * log Λ3
/-- `K_δ(x₂) = log^δ x₂`, `δ₂ = 1.50023`. -/
def K : ℝ := ℓ ^ (1.50023 : ℝ)
/-- the plus-4 `ν(x₂)`. -/
def νP : ℝ := min (4 / (sqrt K * log K)) (1 / (2 * 2.0452 * (10 * log ℓ)))
/-- `β₀(x₂) = 1 - νP`. -/
def β0 : ℝ := 1 - νP

/-- the bracket of v'₀ at `Y = log y`, as in BJSm32155.φ. -/
def φ (Y : ℝ) : ℝ :=
  3.2e-8 / Y ^ 4 + Y ^ 4 * (exp ((β0 - 1) * Y) / β0 + 1.02 * Y ^ 10 / exp (Y / 2) +
    3 * Y ^ 10 / exp (2 * Y / 3))

/-- `v₀(X₃)` with `v'₀ ≤ v`, as in BJSm32155.v0. -/
def v0 (v : ℝ) : ℝ := v * (1 + 1 / (Λ3 ^ 10 * ℓ ^ 5) + 1 / ((1 - 6 / ℓ) * Λ3)) + 3 / Λ3

/-- `m(X₃)`, as in BJSm32155.mX3. -/
def mX3 (v : ℝ) : ℝ :=
  39 * v0 v + 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) + 26 * Λ3 ^ 5 / ℓ ^ 10 +
    88 * Λ3 ^ 5 * (exp (-(8 / 3 * Λ3)) + exp (-(Λ3 / 2))) + 106 / Λ3 ^ 6

lemma exp567_ge : (1.7629 : ℝ) ≤ exp (567 / 1000) := by
  have h := sum_le_exp_of_nonneg (x := (567 / 1000 : ℝ)) (by norm_num) 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢; linarith

lemma exp31567_ge : (5.12 * 10 ^ 13 : ℝ) ≤ exp (31567 / 1000) := by
  have e : exp (31567 / 1000 : ℝ) = exp 1 ^ 31 * exp (567 / 1000) := by
    rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 31 ≤ exp 1 ^ 31 :=
    pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 31
  have h2 := exp567_ge
  rw [e]
  have h3 := mul_le_mul h1 h2 (by norm_num) (by positivity)
  have h4 : (5.12 * 10 ^ 13 : ℝ) ≤ (2.7182818283 : ℝ) ^ 31 * 1.7629 := by norm_num
  linarith

lemma Λ3_ge : (6.4 * 10 ^ 12 : ℝ) ≤ Λ3 := by unfold Λ3; have := exp31567_ge; linarith

lemma log_Λ3 : log Λ3 = 31567 / 1000 - 3 * log 2 := by
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

/-- `29.48755 ≤ log ℓ ≤ 29.48756`. -/
lemma logℓ_bounds : 29.48755 ≤ log ℓ ∧ log ℓ ≤ 29.48756 := by
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

lemma exp736849_ge : (1585.23 : ℝ) ≤ exp 7.36849 := by
  have h := sum_le_exp_of_nonneg (x := (7.36849 : ℝ)) (by norm_num) 26
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

/-- **`νP ℓ ≥ 143.33`**, PROVED. -/
lemma νPℓ_ge : 143.33 ≤ νP * ℓ := by
  obtain ⟨u1, u2⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  set u := log ℓ with hu
  have hK : K = exp (u * 1.50023) := by unfold K; rw [rpow_def_of_pos hℓ]
  have hlogK : log K = 1.50023 * u := by rw [hK, log_exp]; ring
  have hsK : sqrt K = exp (0.750115 * u) := by
    rw [hK, sqrt_eq_rpow, ← exp_mul]; ring_nf
  have hℓe : ℓ = exp u := (exp_log hℓ).symm
  unfold νP
  rw [hsK, hlogK]
  have br1 : 143.33 ≤ 4 / (exp (0.750115 * u) * (1.50023 * u)) * ℓ := by
    rw [hℓe, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e : exp u = exp (0.750115 * u) * exp (0.249885 * u) := by rw [← exp_add]; ring_nf
    rw [e]
    have hE : 1585.23 ≤ exp (0.249885 * u) := by
      have h0 : exp (7.36849 : ℝ) ≤ exp (0.249885 * u) := exp_le_exp.mpr (by linarith)
      linarith [exp736849_ge]
    have hu2 : 1.50023 * u ≤ 44.23814 := by nlinarith
    have hp := exp_pos (0.750115 * u)
    have : 143.33 * (exp (0.750115 * u) * (1.50023 * u)) ≤
        143.33 * (exp (0.750115 * u) * 44.23814) := by gcongr
    nlinarith
  have br2 : 143.33 ≤ 1 / (2 * 2.0452 * (10 * u)) * ℓ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have := ℓ_bounds.1; have := Λ3_ge; nlinarith
  rcases min_choice (4 / (exp (0.750115 * u) * (1.50023 * u))) (1 / (2 * 2.0452 * (10 * u))) with h | h
  · rw [h]; exact br1
  · rw [h]; exact br2

lemma νP_pos : 0 < νP := by
  have := νPℓ_ge; have := ℓ_pos; nlinarith

lemma νP_le : νP ≤ 1 / 1000 := by
  obtain ⟨u1, _⟩ := logℓ_bounds
  unfold νP
  refine (min_le_right _ _).trans ?_
  rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith

/-- `Y⁴ e^{-νP Y}` decreases for `Y ≥ ℓ`, since `νP ℓ ≥ 4`. -/
lemma decay (Y : ℝ) (hY : ℓ ≤ Y) : Y ^ 4 * exp (-νP * Y) ≤ ℓ ^ 4 * exp (-νP * ℓ) := by
  have hℓ := ℓ_pos
  have hν := νPℓ_ge
  have hd : 0 ≤ Y - ℓ := by linarith
  have h1 : Y / ℓ ≤ exp ((Y - ℓ) / ℓ) := by
    have := add_one_le_exp ((Y - ℓ) / ℓ)
    have e : (Y - ℓ) / ℓ + 1 = Y / ℓ := by field_simp; ring
    linarith
  have h2 : (Y / ℓ) ^ 4 ≤ exp (4 * ((Y - ℓ) / ℓ)) := by
    have := pow_le_pow_left₀ (div_nonneg (by linarith) hℓ.le) h1 4
    rw [← exp_nat_mul] at this; push_cast at this; exact this
  have h3 : 4 * ((Y - ℓ) / ℓ) ≤ νP * (Y - ℓ) := by
    rw [← mul_div_assoc, div_le_iff₀ hℓ]; nlinarith
  have h4 : (Y / ℓ) ^ 4 ≤ exp (νP * (Y - ℓ)) := h2.trans (exp_le_exp.mpr h3)
  have e1 : Y ^ 4 = ℓ ^ 4 * (Y / ℓ) ^ 4 := by field_simp
  have e2 : exp (-νP * ℓ) = exp (νP * (Y - ℓ)) * exp (-νP * Y) := by rw [← exp_add]; ring_nf
  rw [e1, e2]
  have := exp_pos (-νP * Y)
  have : 0 ≤ ℓ ^ 4 := by positivity
  calc ℓ ^ 4 * (Y / ℓ) ^ 4 * exp (-νP * Y) ≤ ℓ ^ 4 * exp (νP * (Y - ℓ)) * exp (-νP * Y) := by
        gcongr
    _ = _ := by ring

lemma big_poly (Y : ℝ) (hY : 6 * 10 ^ 12 ≤ Y) : Y ^ 14 / exp (Y / 2) ≤ 1 / 10 ^ 40 := by
  have hE := pow_div_factorial_le_exp (x := Y / 2) (by positivity) 20
  have hf : ((Nat.factorial 20 : ℕ) : ℝ) ≤ 10 ^ 19 := by norm_num [Nat.factorial]
  have h20 : (Y / 2) ^ 20 / 10 ^ 19 ≤ exp (Y / 2) :=
    le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hf) hE
  rw [div_le_iff₀ (exp_pos _)]
  have hY6 : (10 : ℝ) ^ 40 * 2 ^ 20 * 10 ^ 19 ≤ Y ^ 6 := by
    have : (6 * 10 ^ 12 : ℝ) ^ 6 ≤ Y ^ 6 := pow_le_pow_left₀ (by norm_num) hY 6
    have c : (10 : ℝ) ^ 40 * 2 ^ 20 * 10 ^ 19 ≤ (6 * 10 ^ 12) ^ 6 := by norm_num
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

lemma exp_nat_ge (n : ℕ) : 2.7182818283 ^ n ≤ exp (n : ℝ) := by
  rw [← exp_one_pow]; exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le n

lemma exp037976_ge : (1.461915 : ℝ) ≤ exp 0.37976 := by
  have h := sum_le_exp_of_nonneg (x := (0.37976 : ℝ)) (by norm_num) 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢; linarith

/-- **`φ(Y) ≤ 9.54·10⁻¹²` for every `Y ≥ log x₂(X₃)`**, PROVED. -/
theorem phi_le (Y : ℝ) (hY : ℓ ≤ Y) : φ Y ≤ 9.54 / 10 ^ 12 := by
  have hℓ := ℓ_pos
  have hℓ12 : (6.4 * 10 ^ 12 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓ := by
    have := ℓ_bounds.1; have := Λ3_ge; nlinarith
  have hY12 : (6 * 10 ^ 12 : ℝ) ≤ Y := by norm_num at hℓ12; linarith
  have hYp : 0 < Y := by linarith
  have hν1 := νP_le
  have hν0 := νP_pos
  have hb : 0.999 ≤ β0 := by unfold β0; norm_num at hν1 ⊢; linarith
  unfold φ
  have t1 : 3.2e-8 / Y ^ 4 ≤ 1 / 10 ^ 50 := by
    rw [div_le_iff₀ (by positivity)]
    have : (6 * 10 ^ 12 : ℝ) ^ 4 ≤ Y ^ 4 := pow_le_pow_left₀ (by norm_num) hY12 4
    norm_num at this ⊢; nlinarith
  have e2 : (β0 - 1) * Y = -νP * Y := by unfold β0; ring
  rw [e2]
  have d := decay Y hY
  have hu := logℓ_bounds.2
  have hℓ4 : ℓ ^ 4 ≤ exp (4 * 29.48756) := by
    have : ℓ = exp (log ℓ) := (exp_log hℓ).symm
    rw [this, ← exp_nat_mul]; push_cast; exact exp_le_exp.mpr (by linarith)
  have hνℓ : exp (-νP * ℓ) ≤ exp (-143.33) := exp_le_exp.mpr (by have := νPℓ_ge; nlinarith)
  have hcomb : ℓ ^ 4 * exp (-νP * ℓ) ≤ exp (4 * 29.48756) * exp (-143.33) :=
    mul_le_mul hℓ4 hνℓ (exp_pos _).le (exp_pos _).le
  have hx : exp (4 * 29.48756) * exp (-143.33) ≤ 9.51 / 10 ^ 12 := by
    rw [← exp_add]
    have e : (4 * 29.48756 + -143.33 : ℝ) = -((25 : ℕ) : ℝ) - 0.37976 := by norm_num
    rw [e, sub_eq_add_neg, exp_add, exp_neg]
    have a := exp_nat_ge 25
    have b : exp (-0.37976 : ℝ) ≤ 0.684035 := by
      have q := exp037976_ge
      rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]; norm_num at q ⊢; linarith
    have hp : 0 < exp ((25 : ℕ) : ℝ) := exp_pos _
    have c : (exp ((25 : ℕ) : ℝ))⁻¹ ≤ (2.7182818283 ^ 25)⁻¹ := by
      rw [inv_le_inv₀ hp (by positivity)]; exact a
    have : (exp ((25 : ℕ) : ℝ))⁻¹ * exp (-0.37976) ≤ (2.7182818283 ^ 25)⁻¹ * 0.684035 :=
      mul_le_mul c b (exp_pos _).le (by positivity)
    have h25 : ((2.7182818283 : ℝ) ^ 25)⁻¹ * 0.684035 ≤ 9.51 / 10 ^ 12 := by
      rw [inv_mul_le_iff₀ (by positivity)]; norm_num
    linarith
  have t2 : Y ^ 4 * (exp (-νP * Y) / β0) ≤ 9.53 / 10 ^ 12 := by
    have : Y ^ 4 * (exp (-νP * Y) / β0) = (Y ^ 4 * exp (-νP * Y)) / β0 := by ring
    rw [this, div_le_iff₀ (by linarith)]
    have : Y ^ 4 * exp (-νP * Y) ≤ 9.51 / 10 ^ 12 := by linarith
    nlinarith
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
  have e : Y ^ 4 * (exp (-νP * Y) / β0 + 1.02 * Y ^ 10 / exp (Y / 2) + 3 * Y ^ 10 / exp (2 * Y / 3)) =
      Y ^ 4 * (exp (-νP * Y) / β0) + Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) +
        Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) := by ring
  rw [e]
  norm_num at t1 t2 t3 t4 ⊢
  linarith

/-- **`m(X₃) ≤ 3.95·10⁻¹⁰`** for any `v` with `0 ≤ v ≤ 9.54·10⁻¹²`, PROVED. -/
theorem m_le (v : ℝ) (_hv0 : 0 ≤ v) (hv : v ≤ 9.54 / 10 ^ 12) : mX3 v ≤ 395 / 10 ^ 12 := by
  have hΛ := Λ3_ge
  have hℓ12 : (6.4 * 10 ^ 12 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓ := by
    have := ℓ_bounds.1; nlinarith
  have hℓ := ℓ_pos
  unfold mX3 v0
  have a1 : 1 / (Λ3 ^ 10 * ℓ ^ 5) ≤ 1 / 10 ^ 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ Λ3 ^ 10 := one_le_pow₀ (by linarith)
    have : (10 ^ 12 : ℝ) ≤ ℓ ^ 5 := by
      have := pow_le_pow_left₀ (by norm_num) hℓ12 5; norm_num at this ⊢; linarith
    nlinarith
  have a2 : 1 / ((1 - 6 / ℓ) * Λ3) ≤ 1 / 10 ^ 12 := by
    have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; norm_num at hℓ12; linarith
    have h6p : 0 < 1 - 6 / ℓ := by linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have a3 : 3 / Λ3 ≤ 3 / (6.4 * 10 ^ 12) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ
  have b1 : 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) ≤ 1 / 10 ^ 20 := by
    have hlog : 1 ≤ log Λ3 := by rw [log_Λ3]; have := log_two_lt_d9; norm_num at this ⊢; linarith
    have hE2 := pow_div_factorial_le_exp (x := Λ3) (by positivity) 20
    have hf : ((Nat.factorial 20 : ℕ) : ℝ) ≤ 10 ^ 19 := by norm_num [Nat.factorial]
    have h20 : Λ3 ^ 20 / 10 ^ 19 ≤ exp Λ3 :=
      le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hf) hE2
    rw [div_le_iff₀ (by have := exp_pos Λ3; positivity)]
    have hΛ4 : (10 ^ 50 : ℝ) ≤ Λ3 ^ 4 := by
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
    have hΛ5 : (10 ^ 62 : ℝ) ≤ Λ3 ^ 5 := by
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
      9.54 / 10 ^ 12 * (1 + 2 / 10 ^ 12) := by
    have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; norm_num at hℓ12; linarith
    have q1 : 0 ≤ 1 / (Λ3 ^ 10 * ℓ ^ 5) := by positivity
    have q2 : 0 ≤ 1 / ((1 - 6 / ℓ) * Λ3) :=
      div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
    apply mul_le_mul hv (by linarith) (by linarith) (by norm_num)
  norm_num at hv' a3 b1 b2 b3 b4 ⊢
  linarith

/-- v'₀(X₃), the sup of the bracket over `Y ≥ ℓ`. -/
def vS : ℝ := ⨆ Y : Set.Ici ℓ, φ Y

lemma phi_nonneg {Y : ℝ} (hY : ℓ ≤ Y) : 0 ≤ φ Y := by
  have hY0 : 0 < Y := ℓ_pos.trans_le hY
  have hb : 0 < β0 := by unfold β0; have := νP_le; linarith
  unfold φ
  positivity

lemma vS_bounds : 0 ≤ vS ∧ vS ≤ 9.54 / 10 ^ 12 := by
  have : Nonempty (Set.Ici ℓ) := ⟨⟨ℓ, Set.mem_Ici.mpr le_rfl⟩⟩
  have hb : BddAbove (Set.range fun Y : Set.Ici ℓ => φ Y) :=
    ⟨9.54 / 10 ^ 12, by rintro _ ⟨Y, rfl⟩; exact phi_le Y Y.2⟩
  exact ⟨(phi_nonneg le_rfl).trans (le_ciSup hb ⟨ℓ, Set.mem_Ici.mpr le_rfl⟩),
    ciSup_le fun Y => phi_le Y Y.2⟩

lemma mX3_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mX3 v := by
  have hΛ := Λ3_ge
  have hℓ := ℓ_pos
  have hℓ12 : (6.4 * 10 ^ 12 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓ := by
    have := ℓ_bounds.1; nlinarith
  have h6 : 6 / ℓ < 1 := by rw [div_lt_one hℓ]; norm_num at hℓ12; linarith
  have hq : 0 ≤ 1 / ((1 - 6 / ℓ) * Λ3) := by
    apply div_nonneg (by norm_num); apply mul_nonneg (by linarith) (by linarith)
  have hlog : 0 < log Λ3 := log_pos (by linarith)
  have hΛ0 : 0 < Λ3 := by linarith
  unfold mX3 v0
  set q := 1 / ((1 - 6 / ℓ) * Λ3)
  positivity

/-- **`0 ≤ m(X₃) ≤ 3.95·10⁻¹⁰`** at log log X₂ = 31.567, δ₂ = 1.50023, plus-4 ν, PROVED. -/
theorem mX3_vS_bounds : 0 ≤ mX3 vS ∧ mX3 vS ≤ 395 / 10 ^ 12 := by
  obtain ⟨v0, v1⟩ := vS_bounds
  exact ⟨mX3_nonneg v0, m_le _ v0 v1⟩

/-- `log K ≤ 250`. -/
lemma logK_le : log K ≤ 250 := by
  have := logℓ_bounds.2
  unfold K; rw [log_rpow ℓ_pos]; nlinarith

open LeanLab.ChenExplicit.U1483 LeanLab.ChenExplicit.U1486 LeanLab.ChenExplicit.U1490 in
/-- **CONDITIONAL ON `ClassNumberPlus4`, `MeanValueStep`, `BordignonEq9`, `BordignonThm13`**:
every real zero of an even primitive real `L(s, χ)` mod `q`, `4·10⁵ < q ≤ K = log^δ₂ x₂(X₃)`, is
at most `1 - νP`; so `νP` is a legitimate even-character Siegel input of `β₀(x₂)` here. -/
theorem nuP3_siegel (hC : ClassNumberPlus4) (hM : MeanValueStep) (h9 : BordignonEq9)
    (h13 : BordignonThm13) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ K) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - νP := by
  have h := siegel_even_upto_K_plus hC hM h9 h13 logK_le q χ hχ hq hqK β hβ
  have : νP ≤ 4 / (Real.sqrt K * Real.log K) := min_le_left _ _
  linarith

/-- Vacuity: `m_le`'s hypotheses hold at `v = 0` and at `v = vS`. -/
example : mX3 0 ≤ 395 / 10 ^ 12 := m_le 0 le_rfl (by norm_num)

end LeanLab.ChenExplicit.U1498MX3

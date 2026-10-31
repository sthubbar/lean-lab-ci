/-
AI-written Lean code, Claude, 2026-10-18, CLOUD session 20261018T2315Z-cloud11, unit U-5024.
P0009 BJS 2022, arXiv 2207.09452v6, Section 9. F0023.lean proves FINDING F-0023 with
`X₃ = X₂^{1/8}`; Section 9 prints `X₃ = exp(exp 30.62)`, slightly smaller. This file proves the
same failure with the printed `X₃`, as the VERIFY subagent of U-5023 asked.

`mX3Λ Λ v` is Lemma 32's `m(X₃)` written with `Λ = log X₃` as the argument; `mX3P_eq` checks by
`rfl` that F0023's `mX3P ll` is `mX3Λ (e^{ll}/8)`. PROVED at `Λ = e^{30.62}`: `m_ge_X3`,
`m(X₃) ≥ 10⁻⁸` for every `v` at least (72) at `x₂(X₃)`, Python `1.228·10⁻⁸`; `pbar2_X3`,
`ε₂ = 1/51`; and `f0023_printedX3`, the case (b) combination below `-6·10⁻³`, Python
`-8.28·10⁻³`, where Section 9 needs `2·10⁻⁴`. CONDITIONAL only on the lab's transcription of
Theorems 44 (b), 50 (b), 51 with F-0021 and F-0022 applied. Chen's theorem is not in doubt;
Goldbach is open.
-/
import LeanLab.ChenExplicit.F0023

open Real

noncomputable section
namespace LeanLab.ChenExplicit.F0023X3

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS LeanLab.ChenExplicit.Section9
  LeanLab.ChenExplicit.F0023

/-- `log x₂(X₃)` with `Λ = log X₃`, (75). -/
def ℓΛ (Λ : ℝ) : ℝ := Λ - 15 * log Λ
/-- `ν(x₂)`, (91). -/
def νΛ (Λ δ : ℝ) : ℝ :=
  min (100 / (sqrt (ℓΛ Λ ^ δ) * log (ℓΛ Λ ^ δ) ^ 2)) (1 / (2 * 2.0452 * (10 * log (ℓΛ Λ))))
/-- `β₀(x₂)`. -/
def β0Λ (Λ δ : ℝ) : ℝ := 1 - νΛ Λ δ
/-- the bracket of (72). -/
def φΛ (Λ δ Y : ℝ) : ℝ :=
  3.2e-8 / Y ^ 4 + Y ^ 4 * (exp ((β0Λ Λ δ - 1) * Y) / β0Λ Λ δ + 1.02 * Y ^ 10 / exp (Y / 2) +
    3 * Y ^ 10 / exp (2 * Y / 3))
/-- `v₀(X₃)`, (71). -/
def v0Λ (Λ v : ℝ) : ℝ :=
  v * (1 + 1 / (Λ ^ 10 * ℓΛ Λ ^ 5) + 1 / ((1 - 6 / ℓΛ Λ) * Λ)) + 3 / Λ
/-- `m(X₃)`, Lemma 32. -/
def mX3Λ (Λ v : ℝ) : ℝ :=
  39 * v0Λ Λ v + 108 * Λ ^ 16 / (exp Λ * log Λ) + 26 * Λ ^ 5 / ℓΛ Λ ^ 10 +
    88 * Λ ^ 5 * (exp (-(8 / 3 * Λ)) + exp (-(Λ / 2))) + 106 / Λ ^ 6

theorem mX3P_eq (ll v : ℝ) : mX3P ll v = mX3Λ (Λ3P ll) v := rfl
theorem φP_eq (ll δ Y : ℝ) : φP ll δ Y = φΛ (Λ3P ll) δ Y := rfl

/-- the printed `log X₃ = e^{30.62}`. -/
abbrev Λp : ℝ := exp (3062 / 100)

lemma Λp_ge : (10 ^ 13 : ℝ) ≤ Λp := BJS51.exp_big _ (by norm_num)

lemma ℓ_eq : ℓΛ Λp = exp (3062 / 100) - 15 * (3062 / 100) := by
  unfold ℓΛ; rw [log_exp]

lemma ℓ_bounds : Λp * (1 - 1 / 10 ^ 10) ≤ ℓΛ Λp ∧ ℓΛ Λp ≤ Λp := by
  have e : Λp = exp (3062 / 100) := rfl
  have h : (10 ^ 13 : ℝ) ≤ exp (3062 / 100) := Λp_ge
  rw [ℓ_eq, e]; constructor <;> nlinarith

lemma ℓ_pos : 0 < ℓΛ Λp := by have := ℓ_bounds; have := Λp_ge; nlinarith

lemma logℓ_bounds : 30.6199 ≤ log (ℓΛ Λp) ∧ log (ℓΛ Λp) ≤ 30.62 := by
  obtain ⟨h1, h2⟩ := ℓ_bounds
  have hΛ := Λp_ge
  constructor
  · have : log (Λp * (1 - 1 / 10 ^ 10)) ≤ log (ℓΛ Λp) := log_le_log (by positivity) h1
    rw [log_mul (by positivity) (by norm_num), log_exp] at this
    have h3 := Real.one_sub_inv_le_log_of_pos (x := (1 - 1 / 10 ^ 10 : ℝ)) (by norm_num)
    norm_num at h3 this ⊢; linarith
  · have : log (ℓΛ Λp) ≤ log Λp := log_le_log ℓ_pos h2
    rw [log_exp] at this; norm_num at this ⊢; linarith

/-- **`ν ℓ ≤ 144.5`** at the printed `X₃`, true value 144.36. -/
lemma νℓ_le : νΛ Λp δ * ℓΛ Λp ≤ 144.5 := by
  obtain ⟨u1, u2⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  set u := log (ℓΛ Λp) with hu
  have hK : ℓΛ Λp ^ δ = exp (u * 1.478) := by rw [rpow_def_of_pos hℓ]
  have hlogK : log (ℓΛ Λp ^ δ) = 1.478 * u := by rw [hK, log_exp]; ring
  have hsK : sqrt (ℓΛ Λp ^ δ) = exp (0.739 * u) := by
    rw [hK, sqrt_eq_rpow, ← exp_mul]; ring_nf
  have hℓe : ℓΛ Λp = exp u := (exp_log hℓ).symm
  have hmin : νΛ Λp δ ≤ 100 / (exp (0.739 * u) * (1.478 * u) ^ 2) := by
    unfold νΛ; rw [hsK, hlogK]; exact min_le_left _ _
  have hE : exp (0.261 * u) ≤ 2957.3 := by
    have a : exp (0.261 * u) ≤ exp (8 - 0.00803) := exp_le_exp.mpr (by nlinarith)
    have e : exp (8 - 0.00803 : ℝ) = exp ((8 : ℕ) : ℝ) * (exp 0.00803)⁻¹ := by
      rw [sub_eq_add_neg, exp_add, exp_neg]; norm_num
    have b := BJS51.exp_nat_le 8
    have c := add_one_le_exp (0.00803 : ℝ)
    have c' : (exp (0.00803 : ℝ))⁻¹ ≤ (1.00803 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ (exp_pos _) (by norm_num)]; linarith
    have d := mul_le_mul b c' (by positivity) (by positivity)
    have f : (2.7182818286 : ℝ) ^ 8 * (1.00803 : ℝ)⁻¹ ≤ 2957.3 := by norm_num
    rw [e] at a; linarith
  have hu2 : 2048.1 ≤ (1.478 * u) ^ 2 := by nlinarith
  have key : 100 / (exp (0.739 * u) * (1.478 * u) ^ 2) * ℓΛ Λp ≤ 144.5 := by
    rw [hℓe, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : exp u = exp (0.739 * u) * exp (0.261 * u) := by rw [← exp_add]; ring_nf
    rw [e]
    have hp := exp_pos (0.739 * u)
    have : 100 * exp (0.261 * u) ≤ 144.5 * (1.478 * u) ^ 2 := by nlinarith
    nlinarith
  calc νΛ Λp δ * ℓΛ Λp ≤ 100 / (exp (0.739 * u) * (1.478 * u) ^ 2) * ℓΛ Λp :=
        mul_le_mul_of_nonneg_right hmin hℓ.le
    _ ≤ 144.5 := key

lemma ν_pos : 0 < νΛ Λp δ := by
  obtain ⟨u1, _⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  unfold νΛ
  have hK : 0 < ℓΛ Λp ^ δ := by positivity
  have hK1 : 0 < log (ℓΛ Λp ^ δ) := by
    rw [log_rpow hℓ]; exact mul_pos (by norm_num) (by linarith)
  apply lt_min
  · have := sqrt_pos.mpr hK; positivity
  · apply div_pos (by norm_num); nlinarith

lemma ν_lt : νΛ Λp δ < 1 := by
  obtain ⟨u1, _⟩ := logℓ_bounds
  unfold νΛ
  refine (min_le_right _ _).trans_lt ?_
  rw [div_lt_one (by nlinarith)]; nlinarith

lemma phi_ℓ_ge : 2.7 / 10 ^ 10 ≤ φΛ Λp δ (ℓΛ Λp) := by
  obtain ⟨u1, u2⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  have hν := νℓ_le
  have hν0 := ν_pos
  have hν1 := ν_lt
  have hb0 : 0 < β0Λ Λp δ := by unfold β0Λ; linarith
  have hb1 : β0Λ Λp δ ≤ 1 := by unfold β0Λ; linarith
  have hℓ4 : exp (4 * 30.6199) ≤ ℓΛ Λp ^ 4 := by
    have : ℓΛ Λp = exp (log (ℓΛ Λp)) := (exp_log hℓ).symm
    rw [this, ← exp_nat_mul]; push_cast; exact exp_le_exp.mpr (by linarith)
  have e1 : (β0Λ Λp δ - 1) * ℓΛ Λp = -(νΛ Λp δ * ℓΛ Λp) := by unfold β0Λ; ring
  have hx : exp (-144.5) ≤ exp ((β0Λ Λp δ - 1) * ℓΛ Λp) := by
    rw [e1]; exact exp_le_exp.mpr (by linarith)
  have hprod : exp (4 * 30.6199) * exp (-144.5) ≤ ℓΛ Λp ^ 4 * exp ((β0Λ Λp δ - 1) * ℓΛ Λp) :=
    mul_le_mul hℓ4 hx (exp_pos _).le (by positivity)
  have hnum : 2.7 / 10 ^ 10 ≤ exp (4 * 30.6199) * exp (-144.5) := by
    rw [← exp_add]
    have e : (4 * 30.6199 + -144.5 : ℝ) = -((22 : ℕ) : ℝ) + -0.0204 := by norm_num
    rw [e, exp_add, exp_neg]
    have a := BJS51.exp_nat_le 22
    have b := add_one_le_exp (-0.0204 : ℝ)
    have c : ((2.7182818286 : ℝ) ^ 22)⁻¹ ≤ (exp ((22 : ℕ) : ℝ))⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (exp_pos _)]; exact a
    have d := mul_le_mul c b (by norm_num) (by positivity)
    have f : (2.7 / 10 ^ 10 : ℝ) ≤ ((2.7182818286 : ℝ) ^ 22)⁻¹ * (-0.0204 + 1) := by norm_num
    linarith
  have hdiv : ℓΛ Λp ^ 4 * exp ((β0Λ Λp δ - 1) * ℓΛ Λp) ≤
      ℓΛ Λp ^ 4 * (exp ((β0Λ Λp δ - 1) * ℓΛ Λp) / β0Λ Λp δ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [le_div_iff₀ hb0]
    have := exp_pos ((β0Λ Λp δ - 1) * ℓΛ Λp)
    nlinarith
  unfold φΛ
  have t1 : 0 ≤ 3.2e-8 / ℓΛ Λp ^ 4 := by positivity
  have t3 : 0 ≤ ℓΛ Λp ^ 4 * (1.02 * ℓΛ Λp ^ 10 / exp (ℓΛ Λp / 2) +
      3 * ℓΛ Λp ^ 10 / exp (2 * ℓΛ Λp / 3)) := by positivity
  have e : ℓΛ Λp ^ 4 * (exp ((β0Λ Λp δ - 1) * ℓΛ Λp) / β0Λ Λp δ +
      1.02 * ℓΛ Λp ^ 10 / exp (ℓΛ Λp / 2) + 3 * ℓΛ Λp ^ 10 / exp (2 * ℓΛ Λp / 3)) =
      ℓΛ Λp ^ 4 * (exp ((β0Λ Λp δ - 1) * ℓΛ Λp) / β0Λ Λp δ) +
      ℓΛ Λp ^ 4 * (1.02 * ℓΛ Λp ^ 10 / exp (ℓΛ Λp / 2) + 3 * ℓΛ Λp ^ 10 / exp (2 * ℓΛ Λp / 3)) := by
    ring
  rw [e]
  linarith

/-- **`m(X₃) ≥ 10⁻⁸` at the printed `X₃ = exp(exp 30.62)`.** -/
theorem m_ge_X3 (v : ℝ) (hv : φΛ Λp δ (ℓΛ Λp) ≤ v) : 1 / 10 ^ 8 ≤ mX3Λ Λp v := by
  have hφ := phi_ℓ_ge
  have hv1 : 2.7 / 10 ^ 10 ≤ v := hφ.trans hv
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv1
  have hΛ := Λp_ge
  have hℓ := ℓ_pos
  have hℓ13 : (10 ^ 13 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓΛ Λp := by
    have := ℓ_bounds.1; nlinarith
  have h6 : 6 / ℓΛ Λp < 1 := by rw [div_lt_one hℓ]; norm_num at hℓ13; linarith
  have hlog : 0 < log Λp := log_pos (by linarith)
  have hΛ0 : 0 < Λp := by linarith
  have hq : 0 ≤ 1 / ((1 - 6 / ℓΛ Λp) * Λp) := by
    apply div_nonneg (by norm_num); apply mul_nonneg (by linarith) (by linarith)
  have hv0' : v ≤ v0Λ Λp v := by
    unfold v0Λ
    have : 0 ≤ 1 / (Λp ^ 10 * ℓΛ Λp ^ 5) := by positivity
    have : 0 ≤ 3 / Λp := by positivity
    nlinarith
  unfold mX3Λ
  have r : 0 ≤ 108 * Λp ^ 16 / (exp Λp * log Λp) + 26 * Λp ^ 5 / ℓΛ Λp ^ 10 +
      88 * Λp ^ 5 * (exp (-(8 / 3 * Λp)) + exp (-(Λp / 2))) + 106 / Λp ^ 6 := by
    positivity
  have c : (1 : ℝ) / 10 ^ 8 ≤ 39 * (2.7 / 10 ^ 10) := by norm_num
  linarith

/-- `log^δ x₂(X₃)` at the printed `X₃`. -/
def B2X3 : ℝ := ℓΛ Λp ^ δ

theorem pbar2_X3 : BJSEm.pbar B2X3 = 53 := by
  obtain ⟨a, b⟩ := BJS51.pbar_X3
  have e : B2X3 = (exp (3062 / 100) - 15 * (3062 / 100)) ^ (1.478 : ℝ) := by
    unfold B2X3; rw [ℓ_eq]
  apply BJSEm.pbar_eq B2X3 53 59 (by norm_num) (by rw [e]; exact a) (by rw [e]; exact b)
  intro p h1 h2
  interval_cases p <;> norm_num

theorem eps2_X3 : BJSEm.eps B2X3 = 1 / 51 := by unfold BJSEm.eps; rw [pbar2_X3]; norm_num

/-- **FINDING F-0023 at the literally printed Section 9 parameters**: `X₂ = exp(exp 32.7)`,
`X₃ = exp(exp 30.62)`, `δ = 1.478`, `α = 10⁻⁵`, `ε₀ = 10⁻⁴`, Theorems 44 (b), 50 (b), 51 corrected
per F-0021 and F-0022. The case (b) combination is below `-6·10⁻³`; Section 9 needs `2·10⁻⁴`. -/
theorem f0023_printedX3 (a c4s w l1s ls L v : ℝ) (ha : 0 ≤ a) (hc4 : 0 ≤ c4s) (hw : 0 ≤ w)
    (hl1 : 0 ≤ l1s) (hls : 0 ≤ ls) (hL : exp ll ≤ L) (hv : φΛ Λp δ (ℓΛ Λp) ≤ v) :
    cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) a c4s w L (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) l1s ls L (exp ll) / 2 -
      cBP e0p (exp eulerMascheroniConstant) twinC (BJSEm.eps B2X3) BJS.cbar (mX3Λ Λp v) L / 2 <
      -6 / 1000 := by
  have hg1 := g_ge
  have hg2 := g_le
  have hT0 : 0 < twinC := by have := twinC_ge_065; linarith
  have hT := twinC_le_06614
  have hLX := LXp_ge
  have hA := cAbP_le (exp eulerMascheroniConstant) twinC _ a c4s w L (exp ll) hg1 hg2 hT0
    eps1_printed ha hc4 hw hLX hL
  have hQ := cQb_ge (exp eulerMascheroniConstant) twinC _ l1s ls L (exp ll) (by linarith) hT0
    eps1_printed hl1 hls hLX (by linarith)
  have hB := cBP_ge (exp eulerMascheroniConstant) twinC _ BJS.cbar (mX3Λ Λp v) L (by linarith) hT0
    (by norm_num at hT ⊢; linarith) eps2_X3 (by have := BJS.cbar_gt; norm_num at this ⊢; linarith)
    (m_ge_X3 v hv) (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  linarith

/-- Vacuity test. -/
theorem f0023_printedX3_instance :
    cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) 0 0 0 (exp ll) (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) 0 0 (exp ll) (exp ll) / 2 -
      cBP e0p (exp eulerMascheroniConstant) twinC (BJSEm.eps B2X3) BJS.cbar
        (mX3Λ Λp (φΛ Λp δ (ℓΛ Λp))) (exp ll) / 2 < -6 / 1000 :=
  f0023_printedX3 0 0 0 0 0 _ _ le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl

#print axioms mX3P_eq
#print axioms νℓ_le
#print axioms m_ge_X3
#print axioms pbar2_X3
#print axioms eps2_X3
#print axioms f0023_printedX3
#print axioms f0023_printedX3_instance

end LeanLab.ChenExplicit.F0023X3

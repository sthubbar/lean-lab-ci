/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6403, track T1.
P0009 BJS 2022, (121) for Theorem 51 at its own δ₂ = 1.445, at the printed log log X₂ = 32.7,
X₃ = X₂^{1/8}: `ε₂ = 1/51`, since `3·5·…·53 ≤ (log x₂(X₃))^{1.445} < 3·5·…·59`; the lower side is
`1.445 · log x₂(X₃) ≥ 44.2466` against `log(3·5·…·53) = 44.2374`. Theorem 51 states its own
"Let 0 < δ < 2", papers/P0009.txt line 3327, so this δ need not be the δ of the k₁ split.
Also `ℓ_eq`: the ℓ of BJSm3270.lean is F0023's `ℓP 32.7`, by rfl.
Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.F0023
import LeanLab.ChenExplicit.BJSm3270
import LeanLab.ChenExplicit.BJSThm51

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Eps3270

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS LeanLab.ChenExplicit.BJS51

/-- `log^{δ₂} x₂(X₃)`, δ₂ = 1.445. -/
def B2 : ℝ := F0023.ℓP (327 / 10) ^ (1.445 : ℝ)

theorem ℓ_eq : BJSm3270.ℓ = F0023.ℓP (327 / 10) := rfl

theorem eps2_3270 : BJSEm.eps B2 = 1 / 51 := by
  obtain ⟨u1, u2⟩ := F0023.logℓ_bounds
  have hℓ := F0023.ℓ_pos
  have hb : (oddPrimorial 53 : ℝ) ≤ B2 ∧ B2 < (oddPrimorial 59 : ℝ) := by
    unfold B2
    rw [rpow_def_of_pos hℓ, oddPrimorial_53, oddPrimorial_59]
    set u := log (F0023.ℓP F0023.ll)
    have hm : u * 1.445 = 44 + (1.445 * u - 44) := by ring
    rw [hm, exp_add]
    have a1 : (2.7182818283 : ℝ) ^ 44 ≤ exp 44 := by
      rw [show (44 : ℝ) = ((44 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
      exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 44
    have a2 : exp 44 ≤ (2.7182818286 : ℝ) ^ 44 := by
      rw [show (44 : ℝ) = ((44 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
      exact pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 44
    have y0 : 0.2466 ≤ 1.445 * u - 44 := by norm_num at u1 ⊢; linarith
    have y1 : 1.445 * u - 44 ≤ 0.25 := by norm_num at u2 ⊢; linarith
    have q := quadratic_le_exp_of_nonneg (x := 1.445 * u - 44) (by linarith)
    have b1 : (1.2766 : ℝ) ≤ exp (1.445 * u - 44) := by nlinarith
    have b2 : exp (1.445 * u - 44) ≤ exp 1 := exp_le_exp.mpr (by linarith)
    have e1 := exp_one_lt_d9
    have c1 : (16294579238595022365 : ℝ) ≤ 2.7182818283 ^ 44 * 1.2766 := by norm_num
    have c2 : (2.7182818286 : ℝ) ^ 44 * 2.7182818286 < 961380175077106319535 := by norm_num
    have p1 := mul_le_mul a1 b1 (by norm_num) (exp_pos _).le
    have p2 := mul_le_mul a2 (b2.trans e1.le) (exp_pos _).le (by positivity)
    constructor
    · push_cast; linarith
    · push_cast; linarith
  have : BJSEm.pbar B2 = 53 := by
    apply BJSEm.pbar_eq B2 53 59 (by norm_num) hb.1 hb.2
    intro p h1 h2
    interval_cases p <;> norm_num
  unfold BJSEm.eps; rw [this]; norm_num

#print axioms eps2_3270

end LeanLab.ChenExplicit.Eps3270

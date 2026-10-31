/-
AI wrote this Lean code. CODEX task44.
BJS arXiv 2207.09452 v6, eq 121, page 39.
Primorial cutoffs at log log X2 equal 31.567.
-/
import LeanLab.ChenExplicit.F0023
import LeanLab.ChenExplicit.U1498MX3
import LeanLab.ChenExplicit.BJSThm51

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Eps31567

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS LeanLab.ChenExplicit.BJS51

/-- log log X₂ = 31.567. -/
abbrev ll : ℝ := 31567 / 1000

/-- `log^{δ₁} x₁(X₂)`, δ₁ = 1.5306. -/
def B1 : ℝ := (exp ll - 5 * ll) ^ (1.5306 : ℝ)

/-- `log^{δ₂} x₂(X₃)`, δ₂ = 1.50023. -/
def B2 : ℝ := F0023.ℓP ll ^ (1.50023 : ℝ)

theorem ℓ_eq : U1498MX3.ℓ = F0023.ℓP ll := rfl

theorem pbar1_31567 : BJSEm.pbar B1 = 59 := by
  have hE := U1498MX3.exp31567_ge
  have hpos : 0 < exp ll - 5 * ll := by norm_num at hE ⊢; linarith
  have hlo : exp ll * (9999 / 10000) ≤ exp ll - 5 * ll := by norm_num at hE ⊢; nlinarith
  have l2 : ll + log (9999 / 10000) ≤ log (exp ll - 5 * ll) := by
    rw [← log_exp ll, ← log_mul (exp_pos _).ne' (by norm_num), log_exp]
    exact log_le_log (by positivity) hlo
  have l3 : -(1 / 9999 : ℝ) ≤ log (9999 / 10000) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (9999 / 10000 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  have hl : log (exp ll - 5 * ll) ≤ ll := by
    have := log_le_log hpos (show exp ll - 5 * ll ≤ exp ll by norm_num)
    rwa [log_exp] at this
  apply BJSEm.pbar_eq B1 59 61 (by norm_num)
  · unfold B1
    rw [rpow_def_of_pos hpos, BJS51.oddPrimorial_59]
    have hm : log (exp ll - 5 * ll) * 1.5306 = 48 + (1.5306 * log (exp ll - 5 * ll) - 48) := by ring
    rw [hm, exp_add]
    have a1 := BJS51.exp_nat_ge 48
    push_cast at a1
    have b : 0.3162 ≤ 1.5306 * log (exp ll - 5 * ll) - 48 := by norm_num at l2 l3 ⊢; nlinarith
    have b2 := sum_le_exp_of_nonneg (x := 1.5306 * log (exp ll - 5 * ll) - 48) (by linarith) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at b2
    have q2 := pow_le_pow_left₀ (by norm_num) b 2
    have q3 := pow_le_pow_left₀ (by norm_num) b 3
    have b3 : (1.3705 : ℝ) ≤ exp (1.5306 * log (exp ll - 5 * ll) - 48) := by
      norm_num at b2 q2 q3 ⊢; linarith
    have c : (961380175077106319535 : ℝ) ≤ 2.7182818283 ^ 48 * 1.3705 := by norm_num
    have := mul_le_mul a1 b3 (by norm_num) (exp_pos _).le
    push_cast; linarith
  · unfold B1
    rw [rpow_def_of_pos hpos, BJSEm.oddPrimorial_61]
    have h1 : exp (log (exp ll - 5 * ll) * 1.5306) ≤ exp 49 :=
      exp_le_exp.mpr (by norm_num at hl ⊢; nlinarith)
    have h2 : exp (49 : ℝ) = exp 1 ^ 49 := by rw [exp_one_pow]; norm_num
    have h3 : exp 1 ^ 49 ≤ (2.7182818286 : ℝ) ^ 49 :=
      pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 49
    have h4 : (2.7182818286 : ℝ) ^ 49 < 58644190679703485491635 := by norm_num
    push_cast; linarith
  · intro p h1 h2
    interval_cases p; norm_num

theorem eps1_31567 : BJSEm.eps B1 = 1 / 57 := by unfold BJSEm.eps; rw [pbar1_31567]; norm_num

theorem pbar2_31567 : BJSEm.pbar B2 = 53 := by
  obtain ⟨u1, u2⟩ := U1498MX3.logℓ_bounds
  have hℓ := U1498MX3.ℓ_pos
  rw [ℓ_eq] at u1 u2 hℓ
  have hb : (oddPrimorial 53 : ℝ) ≤ B2 ∧ B2 < (oddPrimorial 59 : ℝ) := by
    unfold B2
    rw [rpow_def_of_pos hℓ, oddPrimorial_53, oddPrimorial_59]
    set u := log (F0023.ℓP ll)
    have hm : u * 1.50023 = 44 + (1.50023 * u - 44) := by ring
    rw [hm, exp_add]
    have a1 : (2.7182818283 : ℝ) ^ 44 ≤ exp 44 := by
      rw [show (44 : ℝ) = ((44 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
      exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 44
    have a2 : exp 44 ≤ (2.7182818286 : ℝ) ^ 44 := by
      rw [show (44 : ℝ) = ((44 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
      exact pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 44
    have y0 : 0.23745 ≤ 1.50023 * u - 44 := by norm_num at u1 ⊢; linarith
    have y1 : 1.50023 * u - 44 ≤ 0.25 := by norm_num at u2 ⊢; linarith
    have q := sum_le_exp_of_nonneg (x := 1.50023 * u - 44) (by linarith) 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at q
    have q2 := pow_le_pow_left₀ (by norm_num) y0 2
    have q3 := pow_le_pow_left₀ (by norm_num) y0 3
    have q4 := pow_le_pow_left₀ (by norm_num) y0 4
    have q5 := pow_le_pow_left₀ (by norm_num) y0 5
    have b1 : (1.268 : ℝ) ≤ exp (1.50023 * u - 44) := by
      norm_num at q q2 q3 q4 q5 ⊢; linarith
    have b2 : exp (1.50023 * u - 44) ≤ exp 1 := exp_le_exp.mpr (by linarith)
    have e1 := exp_one_lt_d9
    have c1 : (16294579238595022365 : ℝ) ≤ 2.7182818283 ^ 44 * 1.268 := by norm_num
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
  exact this

theorem eps2_31567 : BJSEm.eps B2 = 1 / 51 := by
  unfold BJSEm.eps; rw [pbar2_31567]; norm_num

#print axioms pbar1_31567
#print axioms pbar2_31567
#print axioms eps1_31567
#print axioms eps2_31567

end LeanLab.ChenExplicit.Eps31567

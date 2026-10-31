/-
AI-written Lean code, Claude, 2026-10-19, CLOUD-built run 20261019T0903Z-22821 of the PC lab, unit U-1045, track T2, a scripted port of At3272Eps.lean of PC run 20261019T0703Z-249, U-1041, to log log X₂ = 32.716, δ = 1.47681, ε₀ = 1.6·10⁻⁴, m(X₃) ≤ 4.64·10⁻¹⁰; numeric lemmas retightened where the build required. The ported header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-19, PC run 20261019T0703Z-249, unit U-1041, a sed port of At3273Eps.lean of U-0989, track T2.
P0009 BJS 2022, (121) at log log X₂ = 32.716, X₃ = X₂^{1/8}, δ = 1.47681, the inputs ε₁, ε₂ of
At32716.margin_bP. PROVED: `eps1_32716`, `ε₁ = 1/57`, since `3·5·…·59 ≤ (log x₁(X₂))^δ < 3·5·…·61`,
the lower side with margin about 0.4·10⁻³ in the exponent, `1.47681 · 32.716 = 48.3153` against
`log(3·5·…·59) = 48.3149`; `eps2_32716`, `ε₂ = 1/51`, `p̄ = 53` at `x₂(X₃)`. Same method as
BJSEps328.lean and BJSEpsM.lean. Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.BJSEpsM

open Real

noncomputable section
namespace LeanLab.ChenExplicit.At32716Eps

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS LeanLab.ChenExplicit.BJS51

/-- `log^δ x₁(X₂)`, `log x₁ = e^{32.716} - 5 · 32.716`, (75). -/
def B1 : ℝ := (exp (32716 / 1000) - 5 * (32716 / 1000)) ^ (1.47681 : ℝ)
/-- `log^δ x₂(X₃)`, `X₃ = X₂^{1/8}`. -/
def B2 : ℝ := (exp (32716 / 1000) / 8 - 15 * (32716 / 1000 - 3 * log 2)) ^ (1.47681 : ℝ)

lemma pbar1_lo : (oddPrimorial 59 : ℝ) ≤ B1 := by
  unfold B1
  set ℓ := exp (32716 / 1000 : ℝ) - 5 * (32716 / 1000) with hℓ
  have hE := BJS328.exp_big' (32716 / 1000) (by norm_num)
  have hpos : 0 < ℓ := by rw [hℓ]; linarith
  have hlo : exp (32716 / 1000) * (1 - 1 / 10 ^ 11) ≤ ℓ := by rw [hℓ]; nlinarith
  have l2 : 32716 / 1000 + log (1 - 1 / 10 ^ 11) ≤ log ℓ := by
    rw [← log_exp (32716 / 1000 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
    exact log_le_log (by positivity) hlo
  have l3 : -(2 / 10 ^ 11 : ℝ) ≤ log (1 - 1 / 10 ^ 11) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (1 - 1 / 10 ^ 11 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  rw [rpow_def_of_pos hpos, oddPrimorial_59]
  have hm : log ℓ * 1.47681 = 48 + (1.47681 * log ℓ - 48) := by ring
  rw [hm, exp_add]
  have a1 := exp_nat_ge 48
  push_cast at a1
  have b : 0.3153 ≤ 1.47681 * log ℓ - 48 := by norm_num at l3 ⊢; nlinarith
  have b2 : (1.3702 : ℝ) ≤ exp (1.47681 * log ℓ - 48) := by
    have h := Real.sum_le_exp_of_nonneg (x := 1.47681 * log ℓ - 48) (by linarith) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    nlinarith [sq_nonneg (1.47681 * log ℓ - 48)]
  have c : (961380175077106319535 : ℝ) ≤ 2.7182818283 ^ 48 * 1.3702 := by norm_num
  have := mul_le_mul a1 b2 (by norm_num) (exp_pos _).le
  push_cast; linarith

lemma B1_lt : B1 < oddPrimorial 61 := by
  unfold B1
  have hE := BJS328.exp_big' (32716 / 1000) (by norm_num)
  have hpos : 0 < exp (32716 / 1000) - 5 * (32716 / 1000 : ℝ) := by linarith
  have hl : log (exp (32716 / 1000) - 5 * (32716 / 1000 : ℝ)) ≤ 32716 / 1000 := by
    have := log_le_log hpos
      (show exp (32716 / 1000) - 5 * (32716 / 1000 : ℝ) ≤ exp (32716 / 1000) by linarith)
    rwa [log_exp] at this
  rw [rpow_def_of_pos hpos, BJSEm.oddPrimorial_61]
  have h1 : exp (log (exp (32716 / 1000) - 5 * (32716 / 1000 : ℝ)) * 1.47681) ≤ exp 49 :=
    exp_le_exp.mpr (by nlinarith)
  have h2 : exp (49 : ℝ) = exp 1 ^ 49 := by rw [exp_one_pow]; norm_num
  have h3 : exp 1 ^ 49 ≤ (2.7182818286 : ℝ) ^ 49 :=
    pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 49
  have h4 : (2.7182818286 : ℝ) ^ 49 < 58644190679703485491635 := by norm_num
  push_cast; linarith

/-- **`ε₁ = 1/57` at log log X₂ = 32.716, δ = 1.47681.** -/
theorem eps1_32716 : BJSEm.eps B1 = 1 / 57 := by
  have : BJSEm.pbar B1 = 59 := by
    apply BJSEm.pbar_eq B1 59 61 (by norm_num) pbar1_lo B1_lt
    intro p h1 h2
    interval_cases p; norm_num
  unfold BJSEm.eps; rw [this]; norm_num

lemma bracket53 (ℓ : ℝ) (hℓ : 0 < ℓ) (h1 : 45 ≤ 1.47681 * log ℓ) (h2 : 1.47681 * log ℓ ≤ 46) :
    (oddPrimorial 53 : ℝ) ≤ ℓ ^ (1.47681 : ℝ) ∧ ℓ ^ (1.47681 : ℝ) < (oddPrimorial 59 : ℝ) := by
  rw [rpow_def_of_pos hℓ, oddPrimorial_53, oddPrimorial_59]
  have hm : log ℓ * 1.47681 = 1.47681 * log ℓ := mul_comm _ _
  rw [hm]
  have a1 := exp_nat_ge 45
  have a2 := exp_nat_le 46
  have b1 : exp ((45 : ℕ) : ℝ) ≤ exp (1.47681 * log ℓ) := exp_le_exp.mpr (by push_cast; linarith)
  have b2 : exp (1.47681 * log ℓ) ≤ exp ((46 : ℕ) : ℝ) := exp_le_exp.mpr (by push_cast; linarith)
  push_cast at a1 a2 b1 b2
  have c1 : (16294579238595022365 : ℝ) ≤ 2.7182818283 ^ 45 := by norm_num
  have c2 : (2.7182818286 : ℝ) ^ 46 < 961380175077106319535 := by norm_num
  constructor
  · push_cast; linarith
  · push_cast; linarith

/-- **`ε₂ = 1/51` at `x₂(X₃)`, `X₃ = X₂^{1/8}`, log log X₂ = 32.716, δ = 1.47681.** -/
theorem eps2_32716 : BJSEm.eps B2 = 1 / 51 := by
  have hb : (oddPrimorial 53 : ℝ) ≤ B2 ∧ B2 < (oddPrimorial 59 : ℝ) := by
    unfold B2
    set ℓ := exp (32716 / 1000 : ℝ) / 8 - 15 * (32716 / 1000 - 3 * log 2)
    have hE := BJS328.exp_big' (32716 / 1000) (by norm_num)
    have l2a := log_two_gt_d9
    have l2b := log_two_lt_d9
    have hpos : 0 < ℓ := by simp only [ℓ]; nlinarith
    have hlo : exp (32716 / 1000) * (1 / 9) ≤ ℓ := by simp only [ℓ]; nlinarith
    have hhi : ℓ ≤ exp (32716 / 1000) * (1 / 8) := by simp only [ℓ]; nlinarith
    have l1 : log ℓ ≤ 32716 / 1000 + log (1 / 8) := by
      rw [← log_exp (32716 / 1000 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
      exact log_le_log hpos hhi
    have l2 : 32716 / 1000 + log (1 / 9) ≤ log ℓ := by
      rw [← log_exp (32716 / 1000 : ℝ), ← log_mul (exp_pos _).ne' (by norm_num)]
      exact log_le_log (by positivity) hlo
    have e8 : log (1 / 8 : ℝ) = -(3 * log 2) := by
      rw [one_div, log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; push_cast; ring
    have e9 : log (1 / 9 : ℝ) = -(2 * log 3) := by
      rw [one_div, log_inv, show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]; push_cast; ring
    have l3 := log_three_lt_d9
    rw [e8] at l1; rw [e9] at l2
    norm_num at l2a l3
    exact bracket53 ℓ hpos (by nlinarith) (by nlinarith)
  have : BJSEm.pbar B2 = 53 := by
    apply BJSEm.pbar_eq B2 53 59 (by norm_num) hb.1 hb.2
    intro p h1 h2; interval_cases p <;> norm_num
  unfold BJSEm.eps; rw [this]; norm_num

#print axioms eps1_32716
#print axioms eps2_32716

end LeanLab.ChenExplicit.At32716Eps

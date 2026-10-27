/-
# Discharging `SchoenfeldUpperSmall`

Unit U-1315, PC run 20261021T0103Z-19411, track T1, ladder rung 5b shared input.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. Known mathematics.

`Bridge.lean` reduced the cited `Dudek2014.Section22.Schoenfeld`, Schoenfeld 1976 Theorem 14 and
(5.5), Dudek 2014 page 6, to `SchoenfeldLower ∧ SchoenfeldUpperSmall`. Here the upper half on the
finite range `[121, 10^8)` is proved with no cited input:
* `lcmUpto_le_three_pow`: `lcm(1, ..., n) ≤ 3^n` for every `n ≤ 10^4`, by one `decide` kernel run
  of an iterated `Nat.lcm` table;
* `psi_le_log3_mul`: hence `ψ(t) ≤ t log 3` for `0 ≤ t < 10^4 + 1`;
* `psi_sub_theta_lt_schoenfeld_small`: by Costa Pereira, `ψ(y) - θ(y) ≤ ψ(√y) + ψ(y^{1/3}) + ψ(y^{1/5})
  ≤ log 3 · (√y + 2 y^{1/3}) < 1.11 √y + 3 y^{1/3}` for `1 ≤ y < 10^8`;
* `schoenfeld_upper_small`: `SchoenfeldUpperSmall`, unconditional;
* `schoenfeld_of_lower`: `Schoenfeld` CONDITIONAL ON `SchoenfeldLower` only, and the converse;
* `schoenfeld_lower_at_121`: the vacuity instance, the inequality of `SchoenfeldLower` at `y = 121`.
Goldbach is open.
-/
import LeanLab.Common.PsiTheta.Bridge

namespace LeanLab.Common.PsiTheta

open Real Chebyshev
open LeanLab.Dudek2014.Section22

/-- One pass of the table: `L` is `lcm(1..n)`, `P` is `3^n`; checks the next `k` rows. -/
def lcmChk : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | k + 1, n, L, P => Nat.ble (Nat.lcm L (n + 1)) (3 * P) && lcmChk k (n + 1) (Nat.lcm L (n + 1)) (3 * P)

lemma lcmUpto_succ (n : ℕ) : Nat.lcmUpto (n + 1) = Nat.lcm (Nat.lcmUpto n) (n + 1) := by
  unfold Nat.lcmUpto
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert]
  simp only [id]; rw [lcm_comm]; rfl

lemma lcmUpto_zero : Nat.lcmUpto 0 = 1 := by simp [Nat.lcmUpto]

lemma lcmChk_sound : ∀ (k n : ℕ), lcmChk k n (Nat.lcmUpto n) (3 ^ n) = true →
    ∀ m, n < m → m ≤ n + k → Nat.lcmUpto m ≤ 3 ^ m := by
  intro k
  induction k with
  | zero => intro n _ m h1 h2; omega
  | succ k ih =>
    intro n h m h1 h2
    simp only [lcmChk, Bool.and_eq_true, Nat.ble_eq] at h
    rw [← lcmUpto_succ, show 3 * 3 ^ n = 3 ^ (n + 1) by ring] at h
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h1) with e | e
    · subst e; exact h.1
    · exact ih (n + 1) h.2 m e (by omega)

/-- The kernel table: `lcm(1..n) ≤ 3^n` for `1 ≤ n ≤ 10^4`. -/
lemma lcmChk_10000 : lcmChk 10000 0 1 1 = true := by decide +kernel

/-- **`lcm(1, ..., n) ≤ 3^n` for every `n ≤ 10^4`.** -/
theorem lcmUpto_le_three_pow {n : ℕ} (hn : n ≤ 10000) : Nat.lcmUpto n ≤ 3 ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [lcmUpto_zero]
  · have := lcmChk_sound 10000 0 (by rw [lcmUpto_zero, pow_zero]; exact lcmChk_10000)
    exact this n h (by omega)

/-- **`ψ(t) ≤ t log 3` for `0 ≤ t < 10001`.** -/
theorem psi_le_log3_mul {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 10001) : ψ t ≤ log 3 * t := by
  rw [psi_eq_psi_coe_floor, psi_eq_log_lcmUpto]
  have hn : ⌊t⌋₊ ≤ 10000 := by
    have := Nat.floor_lt ht0 |>.mpr (by norm_num; exact ht : t < ((10001 : ℕ) : ℝ))
    omega
  have h1 := lcmUpto_le_three_pow hn
  have hpos : (0 : ℝ) < Nat.lcmUpto ⌊t⌋₊ := by exact_mod_cast Nat.lcmUpto_pos _
  have h2 : log (Nat.lcmUpto ⌊t⌋₊ : ℝ) ≤ log ((3 : ℝ) ^ ⌊t⌋₊) :=
    Real.log_le_log hpos (by exact_mod_cast h1)
  rw [Real.log_pow] at h2
  have hf : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have hl3 : 0 ≤ log (3 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith

/-- `log 3 < 1.11`, from `e^{1.11} ≥ e · 1.11 > 3`. -/
lemma log_three_lt : log (3 : ℝ) < 1.11 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 : (1.11 : ℝ) ≤ exp 0.11 := by
    have := Real.add_one_le_exp (0.11 : ℝ); linarith
  have : exp (1.11 : ℝ) = exp 1 * exp 0.11 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith [Real.exp_pos 1]

/-- **Upper half of the cited Schoenfeld bound on `1 ≤ y < 10^8`, unconditional.**
`ψ(y) - θ(y) < 1.11 √y + 3 y^{1/3}`. -/
theorem psi_sub_theta_lt_schoenfeld_small {y : ℝ} (hy : 1 ≤ y) (hy8 : y < 10 ^ 8) :
    ψ y - θ y < 1.11 * √y + 3 * y ^ (1 / 3 : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi y
  have e2 : y ^ (2 : ℝ)⁻¹ = √y := by rw [Real.sqrt_eq_rpow]; norm_num
  have e3 : y ^ (3 : ℝ)⁻¹ = y ^ (1 / 3 : ℝ) := by norm_num
  have e5 : y ^ (5 : ℝ)⁻¹ = y ^ (1 / 5 : ℝ) := by norm_num
  rw [e2, e3, e5] at hCP
  set a := √y with ha
  set b := y ^ (1 / 3 : ℝ) with hb
  set c := y ^ (1 / 5 : ℝ) with hc
  have ha0 : 0 ≤ a := Real.sqrt_nonneg y
  have hb0 : 0 < b := Real.rpow_pos_of_pos hy0 _
  have hc0 : 0 ≤ c := Real.rpow_nonneg hy0.le _
  have ha2 : a ^ 2 = y := Real.sq_sqrt hy0.le
  have ha4 : a < 10001 := by nlinarith
  have hba : b ≤ a := by
    rw [ha, Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have hcb : c ≤ b := Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have pa := psi_le_log3_mul ha0 ha4
  have pb := psi_le_log3_mul hb0.le (by linarith)
  have pc := psi_le_log3_mul hc0 (by linarith)
  have hl := log_three_lt
  have hl0 : 0 ≤ log (3 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith

/-- **`SchoenfeldUpperSmall`, unconditional.** -/
theorem schoenfeld_upper_small : SchoenfeldUpperSmall := by
  intro y hy hy8
  rw [psiF_eq_psi, thetaF_eq_theta]
  exact psi_sub_theta_lt_schoenfeld_small (by linarith) hy8

/-- **The upper half of the cited Schoenfeld bound for every `y ≥ 121`, unconditional.** -/
theorem schoenfeld_upper {y : ℝ} (hy : 121 ≤ y) :
    psiF y - thetaF y < 1.11 * √y + 3 * y ^ (1 / 3 : ℝ) := by
  rcases lt_or_ge y (10 ^ 8) with h | h
  · exact schoenfeld_upper_small y hy h
  · exact schoenfeld_upper_large h

/-- **`Schoenfeld` from its lower half alone.** CONDITIONAL ON `SchoenfeldLower`. -/
theorem schoenfeld_of_lower (hL : SchoenfeldLower) : Schoenfeld :=
  schoenfeld_of_lower_small hL schoenfeld_upper_small

/-- The cited `Schoenfeld` is exactly as strong as `SchoenfeldLower`. -/
theorem schoenfeld_iff_lower : Schoenfeld ↔ SchoenfeldLower :=
  ⟨fun h => (lower_small_of_schoenfeld h).1, schoenfeld_of_lower⟩

/-- `lcm(1..11) = 27720` and `lcm(1..4) = 12`. -/
lemma lcmUpto_11 : Nat.lcmUpto 11 = 27720 := by decide +kernel
lemma lcmUpto_4 : Nat.lcmUpto 4 = 12 := by decide +kernel

/-- **Vacuity instance for `SchoenfeldLower`: its inequality holds at `y = 121`.**
`0.98 √121 = 10.78 < log 27720 + log 12 = ψ(11) + ψ(4) ≤ ψ(121) - θ(121)`. -/
theorem schoenfeld_lower_at_121 : 0.98 * √(121 : ℝ) < psiF 121 - thetaF 121 := by
  rw [psiF_eq_psi, thetaF_eq_theta]
  have hCP := psi_sub_theta_ge_psi_add_psi_add_psi (x := (121 : ℝ)) (by norm_num)
  have e2 : (121 : ℝ) ^ (2 : ℝ)⁻¹ = 11 := by
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      show (121 : ℝ) = 11 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : √(121 : ℝ) = 11 := by
    rw [show (121 : ℝ) = 11 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e3 : (4 : ℝ) ≤ (121 : ℝ) ^ (3 : ℝ)⁻¹ := by
    have h4 : (4 : ℝ) = ((4 : ℝ) ^ (3 : ℝ)) ^ (3 : ℝ)⁻¹ := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    rw [h4]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    norm_num
  have p3 : ψ 4 ≤ ψ ((121 : ℝ) ^ (3 : ℝ)⁻¹) := psi_mono e3
  have p7 := psi_nonneg ((121 : ℝ) ^ (7 : ℝ)⁻¹)
  have p11 : ψ (11 : ℝ) = log 27720 := by
    have := psi_eq_log_lcmUpto 11; push_cast at this; rw [this, lcmUpto_11]; norm_num
  have p4 : ψ (4 : ℝ) = log 12 := by
    have := psi_eq_log_lcmUpto 4; push_cast at this; rw [this, lcmUpto_4]; norm_num
  rw [e2, p11] at hCP
  rw [p4] at p3
  have hlog : (10.78 : ℝ) < log 27720 + log 12 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), Real.lt_log_iff_exp_lt (by norm_num)]
    have h1 : exp (10.78 : ℝ) ≤ exp 11 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : exp (11 : ℝ) = exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 : exp (1 : ℝ) ^ 11 < 2.7182818286 ^ 11 :=
      pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (by norm_num)
    linarith [show (2.7182818286 : ℝ) ^ 11 < 27720 * 12 by norm_num]
  rw [hs]
  linarith

end LeanLab.Common.PsiTheta

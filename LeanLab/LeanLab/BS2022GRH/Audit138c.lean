/-
AI wrote this Lean code for CODEX task138, 2026-10-27.
Domain audit of the sealed Theorems 6 and 7, journal pp. 1231 and 1234.
The paper uses positive table constants and epsilon in its strict sieve range.
The lab predicates allow epsilon = 1 and arbitrary constants.
These are lab transcription questions, not claims of errors in the paper.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Decomp138b
namespace LeanLab.BS2022GRH.Audit138c
open Real Finset Classical ChenThresholdGRH

/-- Theorem 6 bracket audit, p. 1231. Unrestricted C₁ can make its bound negative. -/
theorem b6_negative (N : ℝ) (hN : 1 < N) :
    ∃ C₁ : ℝ, B6J 0.00256 10 1 C₁ (exp (exp 13.375)) N < 0 := by
  let X := exp (exp 13.375)
  have hX : 4e18 ≤ X := X2_ranges.1
  have hX1 : 1 < X := by linarith
  have hlX : 0 < log X := log_pos hX1
  have hlN : 0 < log N := log_pos hN
  have hδ : 0 ≤ 0.62 * log X / X ^ (1 / 16 : ℝ) := by positivity
  have hr : 0 < rX X := by
    unfold rX
    have hp : 1 < X ^ (1 / 8 : ℝ) := Real.one_lt_rpow hX1 (by norm_num)
    exact div_pos (by positivity) (by linarith)
  have hq : 0.16 ≤ qG X := Cert1567.qG_ge X hX
  have hcg : 0 < cGJ X := by
    unfold cGJ pGJ
    have hllX : 0 < log (log X) := by dsimp [X]; rw [log_exp, log_exp]; norm_num
    have hterm : 0 ≤ 0.85 / (√X * log (log X)) := by positivity
    linarith
  have hlog83 : 0 < log (8 / 3 : ℝ) := log_pos (by norm_num)
  let b := (1 + 5e-5) * (1 + 0.62 * log X / X ^ (1 / 16 : ℝ)) * rX X *
      (log (8 / 3) + 64 / log X ^ 2) +
      (1 + 0.62 * log X / X ^ (1 / 16 : ℝ)) * cGJ X / log N ^ (10 - 1 : ℝ)
  have hb : 0 < b := by dsimp [b]; positivity
  have heq (C₁ : ℝ) : B6J 0.00256 10 1 C₁ X N = B6J 0.00256 10 1 0 X N + C₁ * b := by
    unfold B6J l1J l3J
    rw [Cert1567.e2h', Cert1567.e2h']
    dsimp [b]
    ring
  refine ⟨(-B6J 0.00256 10 1 0 X N - 1) / b, ?_⟩
  change B6J 0.00256 10 1 ((-B6J 0.00256 10 1 0 X N - 1) / b) X N < 0
  rw [heq, div_mul_cancel₀ _ hb.ne']
  linarith
/-- The sealed `Thm6J` as it stood before the 2026-10-27 statement fix, kept verbatim for this audit.
U-1580, 2026-10-28: the live `Thm6J` now carries `0 < ε → ε < 1 / 63 →` and `Even n →`. -/
def Thm6JOld : Prop :=
  ∀ (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ), GRH → LinearSieveT4 ε C₁ C₂ → epsJ u ≤ ε →
    0 < α → α < 1 / 24 → 0 < A → Cond19 α A u X₂ → exp (exp 10) ≤ X₂ → X₂ ≤ (n : ℝ) →
    ∑ q ∈ (U7153.Qset n).filter (fun q => ¬ q ∣ n), (U7153.SAq n q : ℝ)
      ≤ 8 * (UNfull n * n / log n ^ 2) * B6J α A ε C₁ X₂ n

/-- Lab transcription audit, CONDITIONAL ON the pre-fix sealed Thm6J, not a disproof of GRH. -/
theorem thm6J_excludes_grh (h6 : Thm6JOld) : ¬ GRH := by
  intro hGRH
  obtain ⟨n, _hnEven, hn⟩ := threshold_nonvacuous
  have hn1 : (1 : ℝ) < n := lt_of_lt_of_le (by linarith [X2_ranges.1]) hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl : 0 < log (n : ℝ) := log_pos hn1
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  have hb : 0 < 8 * (UNfull n * (n : ℝ) / log n ^ 2) := by positivity
  obtain ⟨C₁, hC₁⟩ := b6_negative n hn1
  have heps : epsJ 1500 ≤ 1 := by
    have he : epsJ 1500 < 1 / 8349 := Cert1575.eps1500
    linarith
  have h := h6 0.00256 10 1500 1 C₁ 0 (exp (exp 13.375)) n hGRH
    (Decomp138b.sieve_of_bad_epsilon 1 C₁ 0 (by norm_num)) heps (by norm_num) (by norm_num)
    (by norm_num) cond19_13375 X2_ranges.2 hn
  have hneg := mul_neg_of_pos_of_neg hb hC₁
  have hnonneg : 0 ≤ ∑ q ∈ (U7153.Qset n).filter (fun q => ¬ q ∣ n), (U7153.SAq n q : ℝ) :=
    sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  linarith

/-- The principal value logarithmic integral is nonnegative at every y at least 2. -/
theorem liPV_nonneg {y : ℝ} (hy : 2 ≤ y) : 0 ≤ liPV y := by
  rw [liPV_eq_add hy]
  apply add_nonneg liPV_two_le.1
  apply intervalIntegral.integral_nonneg hy
  intro t ht
  exact one_div_nonneg.mpr (log_nonneg (by linarith [ht.1]))

/-- Theorem 7 bracket audit, p. 1234. Unrestricted C₁ can make its bound negative. -/
theorem b7_negative : ∃ C₁ : ℝ, B7J 0.00256 10 1 C₁ (exp (exp 13.375)) (1 / 2) < 0 := by
  let X := exp (exp 13.375)
  let Y := X ^ (1 / 3 : ℝ)
  have hX : 4e18 ≤ X := X2_ranges.1
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hlX : 0 < log X := log_pos hX1
  have hY0 : 0 < Y := rpow_pos_of_pos hX0 _
  have hlogY : 100 < log Y := by
    dsimp [Y, X]
    rw [← exp_mul, log_exp]
    nlinarith [Journal.exp13375_ge]
  have hY2 : 2 ≤ Y := by
    have he := exp_le_exp.mpr (by linarith : (1 : ℝ) ≤ log Y)
    rw [exp_log hY0] at he
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hli : 0 ≤ liPV Y := liPV_nonneg hY2
  have hslo : 1 ≤ √(1 + (1 / 2 : ℝ)) := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 1 + 1 / 2)
    simpa only [Real.sqrt_one] using h
  have hshi : √(1 + (1 / 2 : ℝ)) ≤ 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) + 1 / 2 ≤ 4)
    norm_num at h ⊢
    exact h
  have hroot0 : 0 ≤ log √(1 + (1 / 2 : ℝ)) := log_nonneg hslo
  have hroot1 : log √(1 + (1 / 2 : ℝ)) ≤ 1 := by
    have h := log_le_log (by linarith : 0 < √(1 + (1 / 2 : ℝ))) hshi
    have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hD : 0 < log Y ^ 2 - log √(1 + (1 / 2 : ℝ)) ^ 2 := by nlinarith
  have hcb : 0 < LeanLab.ChenExplicit.BJS.cbar := by
    have h := LeanLab.ChenExplicit.BJS.cbar_gt
    linarith
  have hlog83 : 0 < log (8 / 3 : ℝ) := log_pos (by norm_num)
  let b := 3 * (1 + 0.06 * log X / X ^ (1 / 6 : ℝ)) * (1 + (1 / 2 : ℝ)) *
    (log Y * (liPV Y + X ^ (1 / 6 : ℝ) * log Y / (8 * π)) / Y) *
    (LeanLab.ChenExplicit.BJS.cbar + 36 / log X ^ 2 + (log (8 / 3) + 64 / log X ^ 2) *
      (log √(1 + (1 / 2 : ℝ)) / (log Y ^ 2 - log √(1 + (1 / 2 : ℝ)) ^ 2) + 27 / log X ^ 2))
  have hb : 0 < b := by dsimp [b]; positivity
  have heq (C₁ : ℝ) : B7J 0.00256 10 1 C₁ X (1 / 2) = B7J 0.00256 10 1 0 X (1 / 2) + C₁ * b := by
    unfold B7J
    dsimp [b, Y]
    ring
  refine ⟨(-B7J 0.00256 10 1 0 X (1 / 2) - 1) / b, ?_⟩
  change B7J 0.00256 10 1 ((-B7J 0.00256 10 1 0 X (1 / 2) - 1) / b) X (1 / 2) < 0
  rw [heq, div_mul_cancel₀ _ hb.ne']
  linarith
/-- The sealed `Thm7J` as it stood before the 2026-10-27 statement fix, kept verbatim for this audit.
U-1580, 2026-10-28: the live `Thm7J` now carries `0 < ε → ε < 1 / 63 →` and `Even n →`. -/
def Thm7JOld : Prop :=
  ∀ (α A u ε C₁ C₂ X₂ ε₁ : ℝ) (n : ℕ), GRH → LinearSieveT4 ε C₁ C₂ → epsJ u ≤ ε →
    0 < ε₁ → ε₁ < 1 → 0 < α → α < 1 / 16 → 0 < A → Cond25 α A u X₂ → exp (exp 10) ≤ X₂ →
    X₂ ≤ (n : ℝ) →
    (U7153.SB n : ℝ) ≤ UNfull n * n / log n ^ 2 * B7J α A ε C₁ X₂ ε₁

/-- Lab transcription audit, CONDITIONAL ON the pre-fix sealed Thm7J, not a disproof of GRH. -/
theorem thm7J_excludes_grh (h7 : Thm7JOld) : ¬ GRH := by
  intro hGRH
  obtain ⟨n, _hnEven, hn⟩ := threshold_nonvacuous
  have hn1 : (1 : ℝ) < n := lt_of_lt_of_le (by linarith [X2_ranges.1]) hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl : 0 < log (n : ℝ) := log_pos hn1
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  have hb : 0 < UNfull n * (n : ℝ) / log n ^ 2 := by positivity
  obtain ⟨C₁, hC₁⟩ := b7_negative
  have heps : epsJ 1500 ≤ 1 := by
    have he : epsJ 1500 < 1 / 8349 := Cert1575.eps1500
    linarith
  have h := h7 0.00256 10 1500 1 C₁ 0 (exp (exp 13.375)) (1 / 2) n hGRH
    (Decomp138b.sieve_of_bad_epsilon 1 C₁ 0 (by norm_num)) heps (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) cond25_13375 X2_ranges.2 hn
  have hneg := mul_neg_of_pos_of_neg hb hC₁
  have hnonneg : 0 ≤ (U7153.SB n : ℝ) := Nat.cast_nonneg _
  linarith

end LeanLab.BS2022GRH.Audit138c

#print axioms LeanLab.BS2022GRH.Audit138c.b6_negative

#print axioms LeanLab.BS2022GRH.Audit138c.liPV_nonneg

#print axioms LeanLab.BS2022GRH.Audit138c.b7_negative

#print axioms LeanLab.BS2022GRH.Audit138c.thm6J_excludes_grh

#print axioms LeanLab.BS2022GRH.Audit138c.thm7J_excludes_grh

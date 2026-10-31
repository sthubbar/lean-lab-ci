/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0932.
P0020 Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488, read in Claude in Chrome in run 20261018T0503Z-16389: the two printed
constants that STATEMENTS.md listed as checked in Python only.

PROVED:
* `lemma4_3_const`: Lemma 4.3, (19/6) exp(8(0.263 - 1/3) + 8 · 0.3246 · e^{0.3246} - 14.66 · 0.3246)
  < 0.563; the value is 0.562137.
* `case3_const`: Case 3, 1 - (s + 3)/(2e^k) · (2ek/(s - 3))^{(s-3)/2} > 0.0563 at s = 14.66,
  k = 2 + log 1.097; the value is 0.0563091, margin 9e-6.
Both MATCH the paper. Goldbach is open.
-/
import Mathlib

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.Campbell43

/-- **Lemma 4.3's constant.** -/
theorem lemma4_3_const :
    19 / 6 * exp (8 * (0.263 - 1 / 3) + 8 * 0.3246 * exp 0.3246 - 14.66 * 0.3246) < 0.563 := by
  have h1 : exp (0.3246 : ℝ) ≤ 1.3836 := by
    have h := Real.exp_bound' (x := (0.3246 : ℝ)) (by norm_num) (by norm_num) (n := 7) (by norm_num)
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have hE : 8 * (0.263 - 1 / 3) + 8 * 0.3246 * exp 0.3246 - 14.66 * 0.3246 ≤ (-1.728 : ℝ) := by
    norm_num; nlinarith
  have h2 : (5.6293 : ℝ) ≤ exp 1.728 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1.728 : ℝ)) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have h3 : exp (8 * (0.263 - 1 / 3) + 8 * 0.3246 * exp 0.3246 - 14.66 * 0.3246) ≤ (exp 1.728)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have h4 : (exp 1.728)⁻¹ ≤ (5.6293 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  have : 19 / 6 * (5.6293 : ℝ)⁻¹ < 0.563 := by norm_num
  nlinarith [exp_pos (8 * (0.263 - 1 / 3) + 8 * 0.3246 * exp 0.3246 - 14.66 * 0.3246)]

lemma log1097_le : log 1.097 ≤ (0.09257927 : ℝ) := by
  have h := abs_log_sub_add_sum_range_le (x := (-0.097 : ℝ)) (by norm_num) 6
  rw [abs_le] at h
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h
  have e : (1 : ℝ) - -0.097 = 1.097 := by norm_num
  norm_num at e
  linarith [h.1]

lemma logx_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 0.97568101) : log x ≤ (-0.0246195 : ℝ) := by
  have hm : log x ≤ log 0.97568101 := log_le_log hx0 hx
  have h := abs_log_sub_add_sum_range_le (x := (1 - 0.97568101 : ℝ)) (by norm_num) 4
  rw [abs_le] at h
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h
  norm_num at hm
  linarith [h.2]

/-- **Case 3's constant**, s = 14.66, k = 2 + log 1.097. -/
theorem case3_const :
    let s : ℝ := 14.66
    let k : ℝ := 2 + log 1.097
    0.0563 < 1 - (s + 3) / (2 * exp k) * (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2) := by
  intro s k
  have hl0 : 0 < log (1.097 : ℝ) := log_pos (by norm_num)
  have hl := log1097_le
  have he1 := exp_one_lt_d9
  have he2 := exp_one_gt_d9
  have hk : exp k = exp 1 ^ 2 * 1.097 := by
    simp only [k]; rw [exp_add, exp_log (by norm_num), exp_one_pow]; norm_num
  have hx0 : 0 < 2 * exp 1 * k / (s - 3) := by
    simp only [s, k]; have := exp_pos 1; positivity
  have hx : 2 * exp 1 * k / (s - 3) ≤ 0.97568101 := by
    simp only [s, k]
    rw [div_le_iff₀ (by norm_num)]
    have : 2 * exp 1 * (2 + log 1.097) ≤ 2 * 2.7182818286 * (2 + 0.09257927) := by
      apply mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    norm_num at this ⊢; linarith
  have hlx := logx_le hx0 hx
  have hpow : (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2) ≤ (exp 0.14353)⁻¹ := by
    rw [rpow_def_of_pos hx0, ← exp_neg]
    apply exp_le_exp.mpr
    simp only [s] at hlx ⊢
    norm_num at hlx ⊢; nlinarith
  have hE : (1.154341 : ℝ) ≤ exp 0.14353 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.14353 : ℝ)) (by norm_num) 10
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hinv : (exp 0.14353)⁻¹ ≤ (1.154341 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hE
  have he2' : (2.7182818283 : ℝ) ^ 2 ≤ exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he2.le 2
  have hc : (s + 3) / (2 * exp k) ≤ 17.66 / (2 * (2.7182818283 ^ 2 * 1.097)) := by
    rw [hk, show s + 3 = (17.66 : ℝ) by norm_num [s]]
    gcongr
  have hc0 : 0 ≤ (s + 3) / (2 * exp k) := by simp only [s]; positivity
  have hp0 : 0 ≤ (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2) := rpow_nonneg hx0.le _
  have := mul_le_mul hc (hpow.trans hinv) hp0 (by norm_num)
  have fin : 17.66 / (2 * ((2.7182818283 : ℝ) ^ 2 * 1.097)) * (1.154341 : ℝ)⁻¹ < 0.9437 := by
    norm_num
  linarith

#print axioms lemma4_3_const
#print axioms case3_const

end LeanLab.AlmostPrimes.Campbell43

/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0933.
P0048 Dudek-Dunn 2026, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720,
read in Claude in Chrome at arxiv.org/html/2602.22720: Theorem 1.3, the Λ² lower bound sieve
with factor 1 - (s+3)/(2e^k) (2ek/(s-3))^{(s-3)/2}; Lemma 2.2, V(z) ≥ 0.2749/log² z for
z ≥ 10¹⁰; and Case 3 of Theorem 3.3, s = 18.4, k = 2 + log 3, z = N^{1/20}.

PROVED:
* `lemma2_2_const`: ½ exp(2 · 0.2366 - 2 · 0.5357) ≥ 0.2749, the last step of Lemma 2.2, from
  Σ 1/p < log log z - 0.2366, Rosser-Schoenfeld, and ½ R(z) < 0.5357; value 0.27490019, margin 2e-7.
* `case3_F`: 1 - (s+3)/(2e^k)(2ek/(s-3))^{(s-3)/2} > 0.0364 at s = 18.4, k = 2 + log 3; value
  0.0367251.
* `case3_main`: 0.2749 · 400 · that factor ≥ 4, the main term 4(N - 1)/log² N of Case 3.
* `case3_s_cond`: s ≥ 2k + 3.
All MATCH the paper. The sieve Theorem 1.3 and Rosser-Schoenfeld stay cited. Goldbach is open.
-/
import Mathlib

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.DDConst

/-- **Lemma 2.2's constant.** -/
theorem lemma2_2_const : (0.2749 : ℝ) ≤ 1 / 2 * exp (2 * 0.2366 - 2 * 0.5357) := by
  have h := Real.exp_bound' (x := (0.5982 : ℝ)) (by norm_num) (by norm_num) (n := 14) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h
  have e : exp (2 * 0.2366 - 2 * 0.5357 : ℝ) = (exp 0.5982)⁻¹ := by rw [← exp_neg]; norm_num
  rw [e]
  have hp := exp_pos (0.5982 : ℝ)
  rw [show (1 : ℝ) / 2 * (exp 0.5982)⁻¹ = 1 / (2 * exp 0.5982) by field_simp,
    le_div_iff₀ (by positivity)]
  norm_num at hp ⊢
  linarith

lemma log3_le : log 3 ≤ (1.0986133 : ℝ) := by
  have h2 := log_two_lt_d9
  have h := abs_log_sub_add_sum_range_le (x := (1 / 3 : ℝ)) (by norm_num) 14
  rw [abs_le] at h
  simp only [sum_range_succ, sum_range_zero] at h
  have e : log 3 = log 2 - log (1 - 1 / 3) := by
    rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, log_div (by norm_num) (by norm_num)]; ring
  norm_num at h e
  linarith [h.1]

lemma logx_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1.093885) : log x ≤ (0.089736 : ℝ) := by
  have hm : log x ≤ log 1.093885 := log_le_log hx0 hx
  have h := abs_log_sub_add_sum_range_le (x := (1 - 1.093885 : ℝ)) (by norm_num) 8
  rw [abs_le] at h
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h hm
  linarith [h.2]

/-- **Case 3's sieve factor** at s = 18.4, k = 2 + log 3. -/
theorem case3_F :
    let s : ℝ := 18.4
    let k : ℝ := 2 + log 3
    0.0364 < 1 - (s + 3) / (2 * exp k) * (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2) := by
  intro s k
  have hl0 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  have hl := log3_le
  have he1 := exp_one_lt_d9
  have he2 := exp_one_gt_d9
  have hk : exp k = exp 1 ^ 2 * 3 := by
    simp only [k]; rw [exp_add, exp_log (by norm_num), exp_one_pow]; norm_num
  have hx0 : 0 < 2 * exp 1 * k / (s - 3) := by
    simp only [s, k]; have := exp_pos 1; positivity
  have hx : 2 * exp 1 * k / (s - 3) ≤ 1.093885 := by
    simp only [s, k]
    rw [div_le_iff₀ (by norm_num)]
    have : 2 * exp 1 * (2 + log 3) ≤ 2 * 2.7182818286 * (2 + 1.0986133) := by
      apply mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    norm_num at this ⊢; linarith
  have hlx := logx_le hx0 hx
  have hpow : (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2) ≤ exp 0.691 := by
    rw [rpow_def_of_pos hx0]
    apply exp_le_exp.mpr
    simp only [s] at hlx ⊢
    norm_num at hlx ⊢; nlinarith
  have hE : exp (0.691 : ℝ) ≤ 1.9958 := by
    have h := Real.exp_bound' (x := (0.691 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have he2' : (2.7182818283 : ℝ) ^ 2 ≤ exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he2.le 2
  have hc : (s + 3) / (2 * exp k) ≤ 21.4 / (2 * (2.7182818283 ^ 2 * 3)) := by
    rw [hk, show s + 3 = (21.4 : ℝ) by norm_num [s]]
    gcongr
  have hp0 : 0 ≤ (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2) := rpow_nonneg hx0.le _
  have := mul_le_mul hc (hpow.trans hE) hp0 (by norm_num)
  have fin : 21.4 / (2 * ((2.7182818283 : ℝ) ^ 2 * 3)) * 1.9958 < 1 - 0.0364 := by norm_num
  linarith

/-- **Case 3's main term**: 0.2749 · 400 · F ≥ 4. -/
theorem case3_main :
    let s : ℝ := 18.4
    let k : ℝ := 2 + log 3
    4 ≤ 0.2749 * 400 * (1 - (s + 3) / (2 * exp k) * (2 * exp 1 * k / (s - 3)) ^ ((s - 3) / 2)) := by
  intro s k
  have := case3_F
  simp only at this
  nlinarith

/-- Theorem 1.3's condition s ≥ 2k + 3 in Case 3. -/
theorem case3_s_cond : 2 * (2 + log 3) + 3 ≤ (18.4 : ℝ) := by
  have := log3_le; norm_num; linarith

#print axioms lemma2_2_const
#print axioms case3_F
#print axioms case3_main
#print axioms case3_s_cond

end LeanLab.AlmostPrimes.DDConst

/-
I-0064: machine-checked lower bounds for the constants of two open conjectures, from the
record tables proved in this folder. Run 20261017T1402Z-26900.
- Granville, van de Lune, te Riele 1989 conjecture p(n) ≤ C log² n · log log n, the lab's
  `GvLtRConjecture`. The Top 50 row n = 258549426916149682, p(n) = 8933 forces C ≥ 3/2.
- Cramér's conjecture in the form g ≤ C log² p for the gap g after the prime p. The record
  gap 1132 after 1693182318746371 forces C ≥ 0.92, if the bound is to hold for every prime
  p with 10^15 ≤ p ≤ 4e18.
Both are lower bounds on constants only; neither conjecture is proved or refuted. The
numerical ratios are KNOWN, about 1.5055 and 0.9206.
AI-written Lean code, Claude, 2026-10-17. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Summary
import LeanLab.Verifications.Top50.GapsSummary

namespace LeanLab.Verifications.Top50.Constants

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Gaps

/-- `(1 + x/k + (x/k)²/2)^k ≤ exp x` for `x ≥ 0`. -/
theorem exp_ge_pow (x : ℝ) (k : ℕ) (hk : 0 < k) (hx : 0 ≤ x) :
    (1 + x / k + (x / k) ^ 2 / 2) ^ k ≤ Real.exp x := by
  have hkx : Real.exp x = Real.exp (x / k) ^ k := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [hkx]
  apply pow_le_pow_left₀ (by positivity)
  exact Real.quadratic_le_exp_of_nonneg (by positivity)

theorem exp_int (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ Real.exp n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n

theorem exp_split (a : ℕ) (f : ℝ) : Real.exp (a + f) = Real.exp a * Real.exp f := Real.exp_add _ _

/-- log 258549426916149682 ≤ 40.1. -/
theorem log_n0 : Real.log (258549426916149682 : ℕ) ≤ 40.1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := exp_int 40
  have h2 := exp_ge_pow 0.1 1 one_pos (by norm_num)
  have : Real.exp 40.1 = Real.exp (40 : ℕ) * Real.exp 0.1 := by
    rw [← exp_split]; norm_num
  rw [this]
  have h3 : (258549426916149682 : ℝ) ≤ 2.7182818283 ^ 40 * (1 + 0.1 / (1 : ℕ) + (0.1 / (1 : ℕ)) ^ 2 / 2) ^ 1 := by
    norm_num
  push_cast
  calc (258549426916149682 : ℝ) ≤ _ := h3
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)

/-- log 40.1 ≤ 3.7. -/
theorem log_401 : Real.log 40.1 ≤ 3.7 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := exp_int 3
  have h2 := exp_ge_pow 0.7 4 (by norm_num) (by norm_num)
  have : Real.exp 3.7 = Real.exp (3 : ℕ) * Real.exp 0.7 := by
    rw [← exp_split]; norm_num
  rw [this]
  have h3 : (40.1 : ℝ) ≤ 2.7182818283 ^ 3 * (1 + 0.7 / (4 : ℕ) + (0.7 / (4 : ℕ)) ^ 2 / 2) ^ 4 := by
    norm_num
  calc (40.1 : ℝ) ≤ _ := h3
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)

/-- log 1693182318746371 ≤ 35.07. -/
theorem log_p1 : Real.log (1693182318746371 : ℕ) ≤ 35.07 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := exp_int 35
  have h2 := exp_ge_pow 0.07 1 one_pos (by norm_num)
  have : Real.exp 35.07 = Real.exp (35 : ℕ) * Real.exp 0.07 := by
    rw [← exp_split]; norm_num
  rw [this]
  have h3 : (1693182318746371 : ℝ) ≤ 2.7182818283 ^ 35 * (1 + 0.07 / (1 : ℕ) + (0.07 / (1 : ℕ)) ^ 2 / 2) ^ 1 := by
    norm_num
  push_cast
  calc (1693182318746371 : ℝ) ≤ _ := h3
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)

/-- If `C · A ≥ v > 0` with `0 < A ≤ M`, then `C ≥ v / M`. -/
theorem const_ge {C A M v : ℝ} (hA : 0 < A) (hAM : A ≤ M) (hv : 0 < v) (h : v ≤ C * A) :
    v / M ≤ C := by
  have hM : 0 < M := lt_of_lt_of_le hA hAM
  rw [div_le_iff₀ hM]
  by_cases hC : C ≤ 0
  · nlinarith
  · push_neg at hC; nlinarith

/-- **GvLtR constant.** Any `C` that bounds `p(n) / (log² n · log log n)` for all even
`n ≥ 16` is at least 3/2, from the Top 50 row p(258549426916149682) = 8933. -/
theorem gvltr_const_ge (C : ℝ) (h : ∀ n : ℕ, Even n → 16 ≤ n →
    (minGB n : ℝ) ≤ C * Real.log n ^ 2 * Real.log (Real.log n)) : 3 / 2 ≤ C := by
  have hn := h 258549426916149682 (by decide) (by norm_num)
  rw [Rows2.minGB_8933] at hn
  have hL := log_n0
  have hL1 : (40 : ℝ) ≤ Real.log (258549426916149682 : ℕ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    have h40 : Real.exp 40 = Real.exp 1 ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h40]
    calc Real.exp 1 ^ 40 ≤ (2.7182818286 : ℝ) ^ 40 := pow_le_pow_left₀ (by positivity) this.le 40
      _ ≤ _ := by norm_num
  have hLL : Real.log (Real.log (258549426916149682 : ℕ)) ≤ 3.7 :=
    le_trans (Real.log_le_log (by linarith) hL) log_401
  have hLL0 : 0 < Real.log (Real.log (258549426916149682 : ℕ)) :=
    Real.log_pos (by linarith)
  have hA : 0 < Real.log (258549426916149682 : ℕ) ^ 2 * Real.log (Real.log (258549426916149682 : ℕ)) := by
    positivity
  have hAM : Real.log (258549426916149682 : ℕ) ^ 2 * Real.log (Real.log (258549426916149682 : ℕ))
      ≤ 40.1 ^ 2 * 3.7 := by
    apply mul_le_mul (pow_le_pow_left₀ (by linarith) hL 2) hLL hLL0.le (by norm_num)
  have := const_ge hA hAM (by norm_num : (0 : ℝ) < ((8933 : ℕ) : ℝ)) (by rw [← mul_assoc]; exact hn)
  have h2 : (3 / 2 : ℝ) ≤ ((8933 : ℕ) : ℝ) / (40.1 ^ 2 * 3.7) := by norm_num
  linarith

/-- **Cramér constant on [10^15, 4e18].** Any `C` with `g ≤ C log² p` for every prime gap
`g` after a prime `p` with `10^15 ≤ p ≤ 4e18` is at least 0.92, from the gap 1132 after
1693182318746371. The lower limit 10^15 keeps tiny primes out: the gap after 2 alone
would force C ≥ 1/log² 2, about 2.08, a VERIFY remark of this run. -/
theorem cramer_const_ge (C : ℝ) (h : ∀ p g : ℕ, IsGapAt p g → 10 ^ 15 ≤ p → p ≤ 4 * 10 ^ 18 →
    (g : ℝ) ≤ C * Real.log p ^ 2) : 0.92 ≤ C := by
  have hg := h 1693182318746371 1132 Gaps3.gap_1693182318746371 (by norm_num) (by norm_num)
  have hL := log_p1
  have hL1 : (1 : ℝ) ≤ Real.log (1693182318746371 : ℕ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    push_cast
    linarith
  have hA : 0 < Real.log (1693182318746371 : ℕ) ^ 2 := by positivity
  have hAM : Real.log (1693182318746371 : ℕ) ^ 2 ≤ 35.07 ^ 2 :=
    pow_le_pow_left₀ (by linarith) hL 2
  have := const_ge hA hAM (by norm_num : (0 : ℝ) < ((1132 : ℕ) : ℝ)) hg
  have h2 : (0.92 : ℝ) ≤ ((1132 : ℕ) : ℝ) / 35.07 ^ 2 := by norm_num
  linarith

end LeanLab.Verifications.Top50.Constants

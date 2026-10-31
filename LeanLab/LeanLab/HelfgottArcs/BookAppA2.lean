import Mathlib

/-!
# Helfgott's book, Appendix A, Sections A.2 and A.3: the arithmetic of Lemmas A.10, A.13, A.15

Unit U-6453, CLOUD 20261020T1318Z-cloud43, P0001 P0013. AI wrote this file.

Source: H. A. Helfgott, The ternary Goldbach problem, book draft of 2019-12-14, Appendix A,
pages 515 to 527, copy papers/P0001-book-AppA.pdf.

* `coeff_identity`: Lemma A.10, page 518, `-24 C(k,3) - 96 C(k,4) - 120 C(k,5) =
  -k(k-1)(k-2)(k² - 3k + 4)` for every `k`, the coefficients of the series (A.29) and (A.31).
* `ratio_three` and `ratio_le`: page 519, the ratio numerator `f(k) = 2(k+1)(k²-k+2)` over
  `(k-2)(k²-3k+4)` is `16` at `k = 3` and at most `3.96` for every real `k ≥ 8`, so
  `r_l(s) ≥ ρ_l(s)`.
* `a32_const`: (A.32), `24 · 8 e^{3/2}/(1 - 16/100) ≤ 1025`.
* `a39_const`: (A.39), `1025/√(7π) · (3/(2e))^{3/4} ≤ 140`.
* `a15_two_sided` and `a16_two_sided`: in the proofs of Lemmas A.15 and A.16, `f(x) = Mh(ix)` on
  `|x| > H` lives on both sides, so `|f(x)x|₁ ≤ 1025/H²`, not the printed `1025/(2H²)`; with the
  two sided value the first term of the printed bound alone already exceeds `(109/H²)²`, and
  `(77/H²)²` for A.16. So the printed constants 109 and 77 do not follow from the printed
  argument. The lemmas themselves still hold numerically by a wide margin, gen/appA15_U6453.out;
  a cosmetic proof slip, FINDINGS F-5037.

Known mathematics; these checks verify printed values only. Ternary Goldbach is a theorem; binary
Goldbach is OPEN.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace LeanLab.HelfgottArcs.BookAppA2
open Real

/-- **Lemma A.10's coefficients.** -/
theorem coeff_identity (k : ℕ) :
    -24 * (k.choose 3 : ℚ) - 96 * k.choose 4 - 120 * k.choose 5 =
      -((k : ℚ) * (k - 1) * (k - 2) * (k ^ 2 - 3 * k + 4)) := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k <;> simp [Nat.choose] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
    have e2 := Nat.choose_succ_right_eq (m + 5) 1
    have e3 := Nat.choose_succ_right_eq (m + 5) 2
    have e4 := Nat.choose_succ_right_eq (m + 5) 3
    have e5 := Nat.choose_succ_right_eq (m + 5) 4
    simp only [Nat.choose_one_right, show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega] at e2 e3 e4 e5
    have q2 : ((m + 5).choose 2 : ℚ) * 2 = (m + 5) * (m + 4) := by exact_mod_cast e2
    have q3 : ((m + 5).choose 3 : ℚ) * 3 = (m + 5).choose 2 * (m + 3) := by exact_mod_cast e3
    have q4 : ((m + 5).choose 4 : ℚ) * 4 = (m + 5).choose 3 * (m + 2) := by exact_mod_cast e4
    have q5 : ((m + 5).choose 5 : ℚ) * 5 = (m + 5).choose 4 * (m + 1) := by exact_mod_cast e5
    have c2 : ((m + 5).choose 2 : ℚ) = (m + 5) * (m + 4) / 2 := by linarith
    have c3 : ((m + 5).choose 3 : ℚ) = (m + 5) * (m + 4) * (m + 3) / 6 := by
      rw [c2] at q3; linarith
    have c4 : ((m + 5).choose 4 : ℚ) = (m + 5) * (m + 4) * (m + 3) * (m + 2) / 24 := by
      rw [c3] at q4; linarith
    have c5 : ((m + 5).choose 5 : ℚ) = (m + 5) * (m + 4) * (m + 3) * (m + 2) * (m + 1) / 120 := by
      rw [c4] at q5; linarith
    rw [c3, c4, c5]; push_cast; ring

/-- The ratio numerator at `k = 3`: `f(3) = 16`. -/
theorem ratio_three : (2 * (3 + 1) * (3 ^ 2 - 3 + 2) : ℝ) / ((3 - 2) * (3 ^ 2 - 3 * 3 + 4)) = 16 := by
  norm_num

/-- **`f(k) ≤ 3.96` for `k ≥ 8`**, so `r_l(s) = 3.96/|s + l + 1| ≥ ρ_l(s)` for `l ≥ 8`. -/
theorem ratio_le {k : ℝ} (hk : 8 ≤ k) :
    2 * (k + 1) * (k ^ 2 - k + 2) ≤ 3.96 * ((k - 2) * (k ^ 2 - 3 * k + 4)) := by
  have h0 : 0 ≤ k - 8 := by linarith
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

lemma exp_three_halves_lt : exp (3 / 2) < 4.484375 := by
  have h1 := exp_one_lt_d9
  have hsq : exp (3 / 2) ^ 2 = exp 1 ^ 3 := by
    rw [← exp_nat_mul, ← exp_nat_mul]; norm_num
  have h3 : exp 1 ^ 3 < 4.484375 ^ 2 := by
    have : exp 1 ^ 3 < 2.7182818286 ^ 3 := by
      have := exp_pos 1
      exact pow_lt_pow_left₀ h1 this.le (by norm_num)
    linarith [show (2.7182818286 : ℝ) ^ 3 < 4.484375 ^ 2 by norm_num]
  have hpos := exp_pos (3 / 2)
  nlinarith

/-- **(A.32)**: `24 · 8 e^{3/2}/(1 - 16/100) ≤ 1025`. -/
theorem a32_const : 24 * 8 * exp (3 / 2) / (1 - 16 / 100) ≤ 1025 := by
  rw [div_le_iff₀ (by norm_num)]
  linarith [exp_three_halves_lt]

/-- **(A.39)**: `1025/√(7π) · (3/(2e))^{3/4} ≤ 140`. -/
theorem a39_const : 1025 / √(7 * π) * (3 / (2 * exp 1)) ^ (3 / 4 : ℝ) ≤ 140 := by
  have hπ := pi_gt_d6
  have he := exp_one_gt_d9
  have he0 : 0 < exp 1 := exp_pos 1
  set q := (3 / (2 * exp 1)) with hq
  have hq0 : 0 < q := by positivity
  set A := 1025 / √(7 * π) * q ^ (3 / 4 : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hs : √(7 * π) ^ 2 = 7 * π := sq_sqrt (by positivity)
  have hq4 : (q ^ (3 / 4 : ℝ)) ^ 4 = q ^ 3 := by
    rw [← rpow_natCast, ← rpow_mul hq0.le]; norm_num
  have hA4 : A ^ 4 = 1025 ^ 4 * q ^ 3 / (7 * π) ^ 2 := by
    rw [hA, div_mul_eq_mul_div, div_pow, mul_pow, hq4, show √(7 * π) ^ 4 = (√(7 * π) ^ 2) ^ 2 by ring, hs]
  have hq3 : q ^ 3 ≤ (3 / (2 * 2.7182818283)) ^ 3 := by
    apply pow_le_pow_left₀ hq0.le
    rw [hq]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hπ2 : (7 * 3.141592 : ℝ) ^ 2 ≤ (7 * π) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have key : A ^ 4 ≤ 140 ^ 4 := by
    rw [hA4, div_le_iff₀ (by positivity)]
    calc 1025 ^ 4 * q ^ 3 ≤ 1025 ^ 4 * (3 / (2 * 2.7182818283)) ^ 3 := by gcongr
      _ ≤ 140 ^ 4 * (7 * 3.141592) ^ 2 := by norm_num
      _ ≤ 140 ^ 4 * (7 * π) ^ 2 := by gcongr
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) key

/-- **Lemma A.15 with the two sided `|f(x)x|₁ = 1025/H²`**: the term `2 |f(x)x|₁² |g|₂² / (2π)³`,
`|g|₂² = π^{3/2}`, alone exceeds `(109/H²)²`. -/
theorem a15_two_sided {H : ℝ} (hH : 0 < H) :
    (109 / H ^ 2) ^ 2 < 2 * (1025 / H ^ 2) ^ 2 * (π * √π) / (2 * π) ^ 3 := by
  have hπ := pi_lt_four
  have hπ0 := pi_pos
  have hsπ : √π < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt hπ0.le hπ
  have hs0 : 0 < √π := sqrt_pos.mpr hπ0
  have hH2 : 0 < H ^ 2 := by positivity
  rw [div_pow, div_pow, lt_div_iff₀ (by positivity)]
  have e : 2 * (1025 ^ 2 / (H ^ 2) ^ 2) * (π * √π) = (1025 ^ 2 / (H ^ 2) ^ 2) * (2 * π * √π) := by ring
  rw [e, show (2 * π) ^ 3 = 8 * π ^ 3 by ring]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right (by positivity)]
  -- 109² · 8 π³ < 1025² · 2 π √π, i.e. 4 · 109² π^{3/2} < 1025²
  have hs2 : √π ^ 2 = π := sq_sqrt hπ0.le
  have : 109 ^ 2 * (8 * π ^ 3) = (2 * π * √π) * (4 * 109 ^ 2 * π * √π) := by
    linear_combination (-(8 * 109 ^ 2 * π ^ 2)) * hs2
  rw [this, mul_comm ((1025 : ℝ) ^ 2)]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  have h8 : π * √π < 8 := by nlinarith
  nlinarith

/-- **Lemma A.16 with the two sided norm**: with `|g|₂² = π^{3/2}/2`, the same term alone exceeds
`(77/H²)²`. -/
theorem a16_two_sided {H : ℝ} (hH : 0 < H) :
    (77 / H ^ 2) ^ 2 < 2 * (1025 / H ^ 2) ^ 2 * (π * √π / 2) / (2 * π) ^ 3 := by
  have hπ := pi_lt_four
  have hπ0 := pi_pos
  have hsπ : √π < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt hπ0.le hπ
  have hs0 : 0 < √π := sqrt_pos.mpr hπ0
  have hH2 : 0 < H ^ 2 := by positivity
  rw [div_pow, div_pow, lt_div_iff₀ (by positivity)]
  have e : 2 * (1025 ^ 2 / (H ^ 2) ^ 2) * (π * √π / 2) = (1025 ^ 2 / (H ^ 2) ^ 2) * (π * √π) := by ring
  rw [e, show (2 * π) ^ 3 = 8 * π ^ 3 by ring]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right (by positivity)]
  have hs2 : √π ^ 2 = π := sq_sqrt hπ0.le
  have : 77 ^ 2 * (8 * π ^ 3) = (π * √π) * (8 * 77 ^ 2 * π * √π) := by
    linear_combination (-(8 * 77 ^ 2 * π ^ 2)) * hs2
  rw [this, mul_comm ((1025 : ℝ) ^ 2)]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  have h8 : π * √π < 8 := by nlinarith
  nlinarith

end LeanLab.HelfgottArcs.BookAppA2

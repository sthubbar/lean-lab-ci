/-
AI wrote the Lean code. Codex task324, 2026-11-09.
Yamada arXiv 1511.03409v2 printed page 24, after eq 104.
QUESTIONS: the eq 103 cross term and the eq 104 envelope conversion.
The printed large conductor envelope times the stated outer log N bound
exceeds its final allocation near the lower threshold.
This result concerns that scalar envelope. Lemma 7.2 remains OPEN.
Binary Goldbach is OPEN.
-/
import Mathlib

open Real
namespace LeanLab.ChenExplicit.Budget324

/-- The displayed bound after Yamada eq 104 exceeds its final allocation at log Y equal log N over two. -/
theorem paper104_budget_fails (L : ℝ) (hL : 0 < L) (hupper : L ≤ exp 37) :
    2 * exp (-145) < (29 / 10 : ℝ) * L ^ 2 / (L / 2) ^ 6 := by
  have hcoef : (2 : ℝ) * exp (-145) * L ^ 4 < (29 / 10 : ℝ) * 2 ^ 6 := by
    have hL4 : L ^ 4 ≤ exp 148 := by
      calc
        _ ≤ exp (37 : ℝ) ^ 4 := pow_le_pow_left₀ hL.le hupper _
        _ = _ := by rw [← exp_nat_mul]; norm_num
    have he3 : exp (3 : ℝ) < 27 := by
      calc
        _ = exp (1 : ℝ) ^ 3 := by rw [← exp_nat_mul]; norm_num
        _ < (3 : ℝ) ^ 3 := pow_lt_pow_left₀ exp_one_lt_three (exp_nonneg _) (by decide)
        _ = _ := by norm_num
    calc
      _ ≤ 2 * exp (-145) * exp 148 := mul_le_mul_of_nonneg_left hL4 (by positivity)
      _ = 2 * exp (3 : ℝ) := by rw [mul_assoc, ← exp_add]; norm_num
      _ < 2 * 27 := by linarith
      _ < _ := by norm_num
  have hid : (29 / 10 : ℝ) * L ^ 2 / (L / 2) ^ 6 = ((29 / 10 : ℝ) * 2 ^ 6) / L ^ 4 := by
    field_simp [hL.ne']
  rw [hid]
  exact (lt_div_iff₀ (pow_pos hL 4)).mpr hcoef

/-- The unnormalized envelope after Yamada page 24 eq 104 exceeds its final allocation. -/
theorem paper104_envelope_exceeds_allocation (L S : ℝ)
    (hL : 0 < L) (hupper : L ≤ exp 37) (hS : 0 < S) :
    2 * exp (-145) * S / (L / 2) ^ 4 <
      ((29 / 10 : ℝ) * S * L / (L / 2) ^ 10) * L := by
  have h := mul_lt_mul_of_pos_right (paper104_budget_fails L hL hupper)
    (div_pos hS (pow_pos (div_pos hL (by norm_num : (0 : ℝ) < 2)) 4))
  convert h using 1 <;> field_simp [hL.ne']

/-- Yamada page 24 eq 103: the cross term exceeds its printed allowance at X equal twice L to the tenth.
In the paper application L is log Y. -/
theorem paper103_cross_term_exceeds_allowance (L Y : ℝ) (hL : 2 ≤ L) (hY : 0 < Y) :
    4 * (2 * L ^ 10) * Y / L ^ 10 <
      sqrt ((2 * L ^ 10) * Y) * (2 * sqrt ((2 * L ^ 10) + Y)) := by
  have hLp : 0 < L := by linarith
  have hX : (16 : ℝ) < 2 * L ^ 10 := by
    have hpow : (2 : ℝ) ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ (by norm_num) hL _
    norm_num at hpow
    linarith
  have hX0 : 0 ≤ 2 * L ^ 10 := by positivity
  have hroot : (4 : ℝ) < sqrt (2 * L ^ 10) := by
    have h := sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 16) hX
    have hs : sqrt (16 : ℝ) = 4 := by norm_num
    rw [hs] at h
    exact h
  have hid : sqrt ((2 * L ^ 10) * Y) * sqrt Y = Y * sqrt (2 * L ^ 10) := by
    rw [sqrt_mul hX0, mul_assoc, mul_self_sqrt hY.le, mul_comm]
  calc
    _ = 8 * Y := by
      field_simp [hLp.ne']
      norm_num
    _ < 2 * (Y * sqrt (2 * L ^ 10)) := by
      nlinarith [mul_lt_mul_of_pos_left hroot hY]
    _ = 2 * sqrt ((2 * L ^ 10) * Y) * sqrt Y := by rw [mul_assoc, hid]
    _ ≤ sqrt ((2 * L ^ 10) * Y) * (2 * sqrt ((2 * L ^ 10) + Y)) := by
      have hs : sqrt Y ≤ sqrt ((2 * L ^ 10) + Y) := sqrt_le_sqrt (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hs (sqrt_nonneg ((2 * L ^ 10) * Y))]

end LeanLab.ChenExplicit.Budget324

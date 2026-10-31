/-
AI wrote this Lean code. Codex task69, 2026-10-25.
The final scalar comparisons in displays 3.8, 3.10 and 3.11, pages 353 to 354.
These do not prove the preceding weighted local integral estimates.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.MinorArithmetic

namespace LeanLab.Zinoviev1997
open Real

/-- A power versus exponential bound extends past a point where the exponential grows faster. -/
theorem power_exp_extend (k : ℕ) (a b C x : ℝ) (ha : 0 < a) (hx : a ≤ x)
    (hk : (k : ℝ) ≤ b * a) (hC : a ^ k < C * Real.exp (b * a)) :
    x ^ k < C * Real.exp (b * x) := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hl := Real.log_le_sub_one_of_pos (show 0 < x / a by positivity)
  have hka : (k : ℝ) / a ≤ b := (div_le_iff₀ ha).mpr hk
  have hmul := mul_le_mul_of_nonneg_right hka (show 0 ≤ x - a by linarith)
  have hlog := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg k)
  have heq : (k : ℝ) * (x / a - 1) = ((k : ℝ) / a) * (x - a) := by field_simp <;> ring
  rw [heq] at hlog
  have he : (x / a) ^ k ≤ Real.exp (b * (x - a)) := by
    have hp := Real.exp_nat_mul (Real.log (x / a)) k
    rw [Real.exp_log (by positivity)] at hp
    rw [← hp]
    exact Real.exp_le_exp.mpr (hlog.trans hmul)
  have hprod := mul_le_mul_of_nonneg_right he (Real.exp_pos (b * a)).le
  rw [← Real.exp_add] at hprod
  have hex : b * (x - a) + b * a = b * x := by ring
  rw [hex] at hprod
  have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ a ^ k by positivity)
  have hid : a ^ k * ((x / a) ^ k * Real.exp (b * a)) = x ^ k * Real.exp (b * a) := by
    rw [div_pow]
    field_simp
  rw [hid] at hm
  have hn := mul_lt_mul_of_pos_right hC (Real.exp_pos (b * x))
  have hh : x ^ k * Real.exp (b * a) < (C * Real.exp (b * x)) * Real.exp (b * a) := by
    nlinarith
  exact lt_of_mul_lt_mul_right hh (Real.exp_pos (b * a)).le

theorem ninth_lt_exp (x : ℝ) (hx : 46 ≤ x) : x ^ 9 < 0.000012 * Real.exp x := by
  have hgen := power_exp_extend 9 46 1 0.000012 x (by norm_num) hx (by norm_num)
  simp only [one_mul] at hgen
  apply hgen
  have he : (2.7182818283 : ℝ) ^ 46 < Real.exp 46 := by
    have h := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (46 : ℕ) ≠ 0)
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  have hn : (46 : ℝ) ^ 9 < 0.000012 * (2.7182818283 : ℝ) ^ 46 := by norm_num
  norm_num only [one_mul]
  linarith

theorem fifteenth_lt_exp (x : ℝ) (hx : 46 ≤ x) :
    x ^ 15 < 0.000012 * Real.exp (1.5 * x) := by
  apply power_exp_extend 15 46 1.5 0.000012 x (by norm_num) hx (by norm_num)
  have he : (2.7182818283 : ℝ) ^ 69 < Real.exp 69 := by
    have h := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (69 : ℕ) ≠ 0)
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  have hn : (46 : ℝ) ^ 15 < 0.000012 * (2.7182818283 : ℝ) ^ 69 := by norm_num
  norm_num only [show (1.5 : ℝ) * 46 = 69 by norm_num]
  linarith

/-- The last scalar comparison in display 3.8. -/
theorem local_error1_budget (N : ℝ) (hN : 10 ^ 20 ≤ N) :
    76 * N * Real.sqrt N * Real.log N ^ 3 < 0.0008 * N ^ 2 := by
  have hn : 0 < N := by linarith
  have hl : 46 ≤ Real.log N := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have h := cube_lt_exp_sharp (Real.log N) hl
  have he : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
    congr 1
    ring
  rw [he] at h
  have hm := mul_lt_mul_of_pos_left h (show 0 < 76 * N * Real.sqrt N by positivity)
  have hs := Real.sq_sqrt hn.le
  nlinarith

/-- The last scalar comparison in display 3.10 after its finite sum estimate. -/
theorem local_error2_budget (N : ℝ) (hN : 10 ^ 20 ≤ N) :
    192 * N * Real.log N ^ 5 * (5.04 * Real.log N ^ 4) < 0.012 * N ^ 2 := by
  have hn : 0 < N := by linarith
  have hl : 46 ≤ Real.log N := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have h := ninth_lt_exp (Real.log N) hl
  rw [Real.exp_log hn] at h
  have hm := mul_lt_mul_of_pos_left h (show 0 < 967.68 * N by positivity)
  have he : 192 * N * Real.log N ^ 5 * (5.04 * Real.log N ^ 4) =
      967.68 * N * Real.log N ^ 9 := by ring
  rw [he]
  nlinarith

/-- The last scalar comparison in display 3.11 after its finite sum estimate. -/
theorem local_error3_budget (N : ℝ) (hN : 10 ^ 20 ≤ N) :
    256 * Real.sqrt N * Real.log N ^ 7 * (0.91 * Real.log N ^ 8) < 0.003 * N ^ 2 := by
  have hn : 0 < N := by linarith
  have hl : 46 ≤ Real.log N := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have h := fifteenth_lt_exp (Real.log N) hl
  have he : Real.exp (1.5 * Real.log N) = N * Real.sqrt N := by
    rw [show 1.5 * Real.log N = Real.log N + Real.log N / 2 by ring, Real.exp_add, Real.exp_log hn]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
    congr 1
    ring
  rw [he] at h
  have hm := mul_lt_mul_of_pos_left h (show 0 < 232.96 * Real.sqrt N by positivity)
  have hs := Real.sq_sqrt hn.le
  have hid : 256 * Real.sqrt N * Real.log N ^ 7 * (0.91 * Real.log N ^ 8) =
      232.96 * Real.sqrt N * Real.log N ^ 15 := by ring
  rw [hid]
  nlinarith

end LeanLab.Zinoviev1997

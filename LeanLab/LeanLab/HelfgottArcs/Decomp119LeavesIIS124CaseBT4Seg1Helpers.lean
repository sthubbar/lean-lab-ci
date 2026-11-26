/-
Proved helpers for the leaf caseBT4_seg1 of Decomp119LeavesIIS124CaseBRatioHigh,
P0013 page 72, case b, on 1e25 ≤ x ≤ 1e26: a Taylor bound on exp 0.7, exp 2.8 < 17,
log 6 ≥ 1.69, bounds on log x on the segment, and the final polynomial inequality
in L = log x with constant 0.0014. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Helpers

namespace LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Seg1Helpers
open Real

/-- Taylor bound for exp 0.7. -/
theorem exp_07_lt : Real.exp 0.7 < 2.014 := by
  have h := Real.exp_bound (x := 0.7) (by rw [abs_of_nonneg (by norm_num)]; norm_num) (n := 7) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

/-- exp 2.8 < 17. -/
theorem exp_28_lt : Real.exp 2.8 < 17 := by
  have h : Real.exp 2.8 = Real.exp 0.7 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h0 := (Real.exp_pos 0.7).le
  calc Real.exp 0.7 ^ 4 ≤ 2.014 ^ 4 := pow_le_pow_left₀ h0 exp_07_lt.le 4
    _ < 17 := by norm_num

/-- log 6 ≥ 1.69, from log 2 > 0.69 and log 3 ≥ 1. -/
theorem log6_ge : 1.69 ≤ Real.log 6 := by
  have h3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have h2 := Real.log_two_gt_d9
  rw [show (6:ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith

/-- log x ≥ 57.53 for x ≥ 1e25. -/
theorem logx_ge1 (x : ℝ) (ha : 1e25 ≤ x) : 57.53 ≤ Real.log x := by
  have h2 : (2:ℝ) ^ 83 ≤ x := le_trans (by norm_num) ha
  have := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at this
  have hl := Real.log_two_gt_d9
  push_cast at this; linarith

/-- log x ≤ 60.31 for x ≤ 1e26. -/
theorem logx_le1 (x : ℝ) (hx : 0 < x) (hb : x ≤ 1e26) : Real.log x ≤ 60.31 := by
  have h2 : x ≤ (2:ℝ) ^ 87 := le_trans hb (by norm_num)
  have := Real.log_le_log hx h2
  rw [Real.log_pow] at this
  have hl := Real.log_two_lt_d9
  push_cast at this; linarith

/-- The final polynomial inequality in L = log x for caseBT4_seg1. -/
theorem poly1 (L : ℝ) (h1 : 57.53 ≤ L) (F A B c : ℝ)
    (_hF0 : 0 ≤ F) (hF : F ≤ 1.8222 * (3.05 + (L / 3 - 1.69 - 21) / 21) + 2.50637 / 2.8)
    (hA0 : 0 ≤ A) (hA : A ≤ 2 + 7.12 + L / 3) (hB : 2.95 ≤ B) (hc : 1224.5 ≤ c) :
    (1.93768 : ℝ) ^ 2 * (2 * F) * (A / B) / c ≤ 0.0014 ^ 2 * L ^ 3 := by
  have hB0 : 0 < B := by linarith
  have hc0 : 0 < c := by linarith
  have heq : (1.93768 : ℝ) ^ 2 * (2 * F) * (A / B) / c = 1.93768 ^ 2 * 2 * (F * A) / (B * c) := by
    field_simp
  rw [heq, div_le_iff₀ (by positivity)]
  have hFA : F * A ≤ (1.8222 * (3.05 + (L / 3 - 1.69 - 21) / 21) + 2.50637 / 2.8) * (2 + 7.12 + L / 3) :=
    mul_le_mul hF hA hA0 (by nlinarith)
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have hBc : 2.95 * 1224.5 ≤ B * c := by nlinarith
  have key : (1.93768 : ℝ) ^ 2 * 2 * ((1.8222 * (3.05 + (L / 3 - 1.69 - 21) / 21) + 2.50637 / 2.8) * (2 + 7.12 + L / 3))
      ≤ 0.0014 ^ 2 * L ^ 3 * (2.95 * 1224.5) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1), mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)) (sub_nonneg.2 h1)]
  nlinarith [mul_le_mul_of_nonneg_left hBc (by positivity : (0:ℝ) ≤ 0.0014 ^ 2 * L ^ 3)]

end LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Seg1Helpers

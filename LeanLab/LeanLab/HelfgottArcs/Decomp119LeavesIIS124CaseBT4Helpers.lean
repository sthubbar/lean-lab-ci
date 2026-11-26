/-
Proved helpers for the leaf caseBT4_seg3 of Decomp119LeavesIIS124CaseBRatioHigh,
P0013 page 72, case b: an upper bound on exp of the Euler Mascheroni constant from
the Mathlib upper sequence at n = 32, Taylor bounds on exp at 0.5, 0.6 and 0.95,
bounds on log 6, log 21, log 8/3, log of 500 sqrt 6 and log x on 3e27 ≤ x ≤ 1e30,
and the final polynomial inequality in L = log x. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseB

namespace LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Helpers
open Real

/-- The Euler Mascheroni constant is below 0.6, from harmonic 32 minus log 32. -/
theorem gamma_lt_06 : Real.eulerMascheroniConstant < 0.6 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 32
  have h1 : Real.eulerMascheroniSeq' 32 = (harmonic 32 : ℝ) - Real.log 32 := by
    simp [Real.eulerMascheroniSeq']
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have hH2 : (harmonic 32 : ℚ) < 4.0657 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hH3 : (harmonic 32 : ℝ) < 4.0657 := by
    have := (Rat.cast_lt (K := ℝ)).2 hH2
    rw [show ((4.0657 : ℚ) : ℝ) = 4.0657 by norm_num] at this
    exact this
  have hl := Real.log_two_gt_d9
  rw [h1, h32] at h
  linarith

/-- Taylor bound for exp 0.6. -/
theorem exp_06_lt : Real.exp 0.6 < 1.8222 := by
  have h := Real.exp_bound (x := 0.6) (by rw [abs_of_nonneg (by norm_num)]; norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

/-- exp γ < 1.8222. -/
theorem exp_gamma_lt : Real.exp Real.eulerMascheroniConstant < 1.8222 :=
  (Real.exp_lt_exp.2 gamma_lt_06).trans exp_06_lt

/-- Taylor bound for exp 0.95. -/
theorem exp_09_lt : Real.exp 0.95 < 2.6 := by
  have h := Real.exp_bound (x := 0.95) (by rw [abs_of_nonneg (by norm_num)]; norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

/-- Taylor bound for exp 0.5. -/
theorem exp_05_lt : Real.exp 0.5 < 1.6488 := by
  have h := Real.exp_bound (x := 0.5) (by rw [abs_of_nonneg (by norm_num)]; norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

/-- e > 2.7182818283. -/
theorem e_gt : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9

/-- exp n ≥ 2.7182818283^n. -/
theorem exp_nat_ge (n : ℕ) : 2.7182818283 ^ n ≤ Real.exp n := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) e_gt.le n

/-- log 8/3 ≥ 0.95. -/
theorem log_83_ge : 0.95 ≤ Real.log (8 / 3) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [exp_09_lt]

/-- log 6 ≤ 2. -/
theorem log6_le : Real.log 6 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := exp_nat_ge 2; norm_num at this ⊢; linarith

/-- log 21 ≤ 3.05. -/
theorem log21_le : Real.log 21 ≤ 3.05 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h3 := exp_nat_ge 3
  have h1 := Real.add_one_le_exp (0.05 : ℝ)
  rw [show (3.05 : ℝ) = (3 : ℕ) + 0.05 by norm_num, Real.exp_add]
  have : (0:ℝ) ≤ Real.exp 3 := (Real.exp_pos _).le
  norm_num at h3 ⊢; nlinarith

/-- exp 2.5 < 13. -/
theorem exp_25_lt : Real.exp 2.5 < 13 := by
  have h : Real.exp 2.5 = Real.exp 0.5 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h0 := (Real.exp_pos 0.5).le
  calc Real.exp 0.5 ^ 5 ≤ 1.6488 ^ 5 := pow_le_pow_left₀ h0 exp_05_lt.le 5
    _ < 13 := by norm_num

/-- log of 500 sqrt 6 is at most 7.12. -/
theorem logc_le : Real.log (500 * Real.sqrt 6) ≤ 7.12 := by
  have hs : Real.sqrt 6 ≤ 2.45 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 6 := by positivity
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h7 := exp_nat_ge 7
  have h1 := Real.add_one_le_exp (0.12 : ℝ)
  rw [show (7.12 : ℝ) = (7 : ℕ) + 0.12 by norm_num, Real.exp_add]
  have : (0:ℝ) ≤ Real.exp 7 := (Real.exp_pos _).le
  norm_num at h7 ⊢; nlinarith

/-- log x ≥ 63.07 for x ≥ 3e27. -/
theorem logx_ge (x : ℝ) (ha : 3e27 ≤ x) : 63.07 ≤ Real.log x := by
  have h2 : (2:ℝ) ^ 91 ≤ x := le_trans (by norm_num) ha
  have := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at this
  have hl := Real.log_two_gt_d9
  push_cast at this; linarith

/-- log x ≤ 69.32 for x ≤ 1e30. -/
theorem logx_le (x : ℝ) (hx : 0 < x) (hb : x ≤ 1e30) : Real.log x ≤ 69.32 := by
  have h2 : x ≤ (2:ℝ) ^ 100 := le_trans hb (by norm_num)
  have := Real.log_le_log hx h2
  rw [Real.log_pow] at this
  have hl := Real.log_two_lt_d9
  push_cast at this; linarith

/-- The final polynomial inequality in L = log x for caseBT4_seg3. -/
theorem poly (L : ℝ) (h1 : 63.07 ≤ L) (_h2 : L ≤ 69.32) (F A B c : ℝ)
    (_hF0 : 0 ≤ F) (hF : F ≤ 1.8222 * (3.05 + (L / 3 - 21) / 21) + 2.50637 / 2.5)
    (hA0 : 0 ≤ A) (hA : A ≤ 2 + 7.12 + L / 3) (hB : 2.95 ≤ B) (hc : 1224.5 ≤ c) :
    (1.93768 : ℝ) ^ 2 * (2 * F) * (A / B) / c ≤ 0.0013 ^ 2 * L ^ 3 := by
  have hB0 : 0 < B := by linarith
  have hc0 : 0 < c := by linarith
  have heq : (1.93768 : ℝ) ^ 2 * (2 * F) * (A / B) / c = 1.93768 ^ 2 * 2 * (F * A) / (B * c) := by
    field_simp
  rw [heq, div_le_iff₀ (by positivity)]
  have hFA : F * A ≤ (1.8222 * (3.05 + (L / 3 - 21) / 21) + 2.50637 / 2.5) * (2 + 7.12 + L / 3) :=
    mul_le_mul hF hA hA0 (by nlinarith)
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have hBc : 2.95 * 1224.5 ≤ B * c := by nlinarith
  have key : (1.93768 : ℝ) ^ 2 * 2 * ((1.8222 * (3.05 + (L / 3 - 21) / 21) + 2.50637 / 2.5) * (2 + 7.12 + L / 3))
      ≤ 0.0013 ^ 2 * L ^ 3 * (2.95 * 1224.5) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1), mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)) (sub_nonneg.2 h1)]
  nlinarith [mul_le_mul_of_nonneg_left hBc (by positivity : (0:ℝ) ≤ 0.0013 ^ 2 * L ^ 3)]

end LeanLab.HelfgottArcs.Decomp119LeavesIIS124CaseBT4Helpers

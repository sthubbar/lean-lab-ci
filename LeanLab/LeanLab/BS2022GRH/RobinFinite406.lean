/- AI wrote this Lean code for CODEX task406. Goldbach is open.
The ten finite primorial checks in Robin Theorem 11, p. 380.
https://doi.org/10.4064/aa-42-4-367-389 -/
import LeanLab.BS2022GRH.PaperInputs148

namespace LeanLab.BS2022GRH.Decomp406c
open Real Finset Classical
noncomputable section

/-- The product N_k of the first k primes, Robin p. 380 before Theorem 10. -/
def primeProduct (k : ℕ) : ℕ := ∏ i ∈ range k, Nat.nth Nat.Prime i

end
end LeanLab.BS2022GRH.Decomp406c

namespace LeanLab.BS2022GRH.RobinFinite406
open Real Finset Classical Decomp406c
noncomputable section

/-- Rational Taylor lower certificate used in Robin's finite checks on p. 380. -/
theorem exp_shift_lower (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (2.7182818283 : ℝ) ^ m * (∑ i ∈ range 12, x ^ i / i.factorial) ≤
      exp ((m : ℝ) + x) := by
  have hm := exp_nat_mul (1 : ℝ) m
  simp only [mul_one] at hm
  rw [exp_add, hm]
  have he : (2.7182818283 : ℝ) ^ m ≤ exp 1 ^ m :=
    pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le m
  exact mul_le_mul he (sum_le_exp_of_nonneg hx 12)
    (sum_nonneg (fun _ _ => by positivity)) (by positivity)

/-- Rational Taylor upper certificate used in Robin's finite checks on p. 380. -/
theorem exp_shift_upper (m : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    exp ((m : ℝ) + x) ≤ (2.7182818286 : ℝ) ^ m *
      ((∑ i ∈ range 12, x ^ i / i.factorial) + x ^ 12 * 13 / (Nat.factorial 12 * 12)) := by
  have hm := exp_nat_mul (1 : ℝ) m
  simp only [mul_one] at hm
  rw [exp_add, hm]
  have he : exp 1 ^ m ≤ (2.7182818286 : ℝ) ^ m :=
    pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le m
  have hb : exp x ≤ (∑ i ∈ range 12, x ^ i / i.factorial) +
      x ^ 12 * 13 / (Nat.factorial 12 * 12) := by
    convert exp_bound' hx hx1 (by norm_num : 0 < (12 : ℕ)) using 1 <;> norm_num
  exact mul_le_mul he hb (exp_pos _).le (by positivity)

/-- The ten finite bounds explicitly used in Robin Theorem 11, p. 380.
Every logarithm enclosure follows from rational Taylor bounds checked by the kernel. -/
theorem finite_ratio (k : ℕ) (hk : 3 ≤ k) (hk12 : k ≤ 12) :
    (k : ℝ) * log (log (primeProduct k)) / log (primeProduct k) ≤ 1.38402 := by
  have h5 : Nat.nth Nat.Prime 5 = 13 := by
    have hc : Nat.count Nat.Prime 13 = 5 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 13)
  have h6 : Nat.nth Nat.Prime 6 = 17 := by
    have hc : Nat.count Nat.Prime 17 = 6 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 17)
  have h7 : Nat.nth Nat.Prime 7 = 19 := by
    have hc : Nat.count Nat.Prime 19 = 7 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 19)
  have h8 : Nat.nth Nat.Prime 8 = 23 := by
    have hc : Nat.count Nat.Prime 23 = 8 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 23)
  have h9 : Nat.nth Nat.Prime 9 = 29 := by
    have hc : Nat.count Nat.Prime 29 = 9 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 29)
  have h10 : Nat.nth Nat.Prime 10 = 31 := by
    have hc : Nat.count Nat.Prime 31 = 10 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 31)
  have h11 : Nat.nth Nat.Prime 11 = 37 := by
    have hc : Nat.count Nat.Prime 37 = 11 := by decide
    simpa only [hc] using Nat.nth_count (by decide : Nat.Prime 37)
  interval_cases k
  · have hp : primeProduct 3 = 30 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (3.4011972 : ℝ) ≤ log 30 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 30)]
      have h := exp_shift_upper 3 0.4011972 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (30 : ℝ) ≤ 3.4011974 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 30)]
      have h := exp_shift_lower 3 0.4011974 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (3.4011974 : ℝ) ≤ 1.2241276 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3.4011974)]
      have h := exp_shift_lower 1 0.2241276 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (30 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 4 = 210 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (5.3471074 : ℝ) ≤ log 210 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 210)]
      have h := exp_shift_upper 5 0.3471074 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (210 : ℝ) ≤ 5.3471076 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 210)]
      have h := exp_shift_lower 5 0.3471076 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (5.3471076 : ℝ) ≤ 1.6765558 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 5.3471076)]
      have h := exp_shift_lower 1 0.6765558 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (210 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 5 = 2310 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (7.7450027 : ℝ) ≤ log 2310 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2310)]
      have h := exp_shift_upper 7 0.7450027 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (2310 : ℝ) ≤ 7.7450029 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2310)]
      have h := exp_shift_lower 7 0.7450029 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (7.7450029 : ℝ) ≤ 2.0470479 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 7.7450029)]
      have h := exp_shift_lower 2 0.0470479 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (2310 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 6 = 30030 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (10.3099520 : ℝ) ≤ log 30030 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 30030)]
      have h := exp_shift_upper 10 0.3099520 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (30030 : ℝ) ≤ 10.3099522 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 30030)]
      have h := exp_shift_lower 10 0.3099522 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (10.3099522 : ℝ) ≤ 2.3331097 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10.3099522)]
      have h := exp_shift_lower 2 0.3331097 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (30030 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 7 = 510510 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (13.1431654 : ℝ) ≤ log 510510 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 510510)]
      have h := exp_shift_upper 13 0.1431654 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (510510 : ℝ) ≤ 13.1431656 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 510510)]
      have h := exp_shift_lower 13 0.1431656 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (13.1431656 : ℝ) ≤ 2.5759019 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 13.1431656)]
      have h := exp_shift_lower 2 0.5759019 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (510510 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 8 = 9699690 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (16.0876043 : ℝ) ≤ log 9699690 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 9699690)]
      have h := exp_shift_upper 16 0.0876043 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (9699690 : ℝ) ≤ 16.0876045 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 9699690)]
      have h := exp_shift_lower 16 0.0876045 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (16.0876045 : ℝ) ≤ 2.7780491 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 16.0876045)]
      have h := exp_shift_lower 2 0.7780491 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (9699690 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 9 = 223092870 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (19.2230986 : ℝ) ≤ log 223092870 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 223092870)]
      have h := exp_shift_upper 19 0.2230986 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (223092870 : ℝ) ≤ 19.2230988 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 223092870)]
      have h := exp_shift_lower 19 0.2230988 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (19.2230988 : ℝ) ≤ 2.9561127 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 19.2230988)]
      have h := exp_shift_lower 2 0.9561127 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (223092870 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 10 = 6469693230 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (22.5903944 : ℝ) ≤ log 6469693230 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 6469693230)]
      have h := exp_shift_upper 22 0.5903944 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (6469693230 : ℝ) ≤ 22.5903946 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 6469693230)]
      have h := exp_shift_lower 22 0.5903946 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (22.5903946 : ℝ) ≤ 3.1175248 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 22.5903946)]
      have h := exp_shift_lower 3 0.1175248 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (6469693230 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 11 = 200560490130 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (26.0243816 : ℝ) ≤ log 200560490130 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 200560490130)]
      have h := exp_shift_upper 26 0.0243816 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (200560490130 : ℝ) ≤ 26.0243818 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 200560490130)]
      have h := exp_shift_lower 26 0.0243818 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (26.0243818 : ℝ) ≤ 3.2590339 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 26.0243818)]
      have h := exp_shift_lower 3 0.2590339 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (200560490130 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  · have hp : primeProduct 12 = 7420738134810 := by
      norm_num [primeProduct, prod_range_succ, h5, h6, h7, h8, h9, h10, h11]
    rw [hp]
    norm_num only [Nat.cast_ofNat]
    have hlo : (29.6352995 : ℝ) ≤ log 7420738134810 := by
      rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 7420738134810)]
      have h := exp_shift_upper 29 0.6352995 (by norm_num) (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hhi : log (7420738134810 : ℝ) ≤ 29.6352997 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 7420738134810)]
      have h := exp_shift_lower 29 0.6352997 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hu : log (29.6352997 : ℝ) ≤ 3.3889663 := by
      rw [log_le_iff_le_exp (by norm_num : (0 : ℝ) < 29.6352997)]
      have h := exp_shift_lower 3 0.3889663 (by norm_num)
      norm_num [sum_range_succ, Nat.factorial] at h ⊢
      linarith only [h]
    have hlog : 0 < log (7420738134810 : ℝ) := by linarith
    have hll := (log_le_log hlog hhi).trans hu
    apply (div_le_iff₀ hlog).mpr
    nlinarith

end
end LeanLab.BS2022GRH.RobinFinite406

#print axioms LeanLab.BS2022GRH.Decomp406c.primeProduct
#print axioms LeanLab.BS2022GRH.RobinFinite406.exp_shift_lower
#print axioms LeanLab.BS2022GRH.RobinFinite406.exp_shift_upper
#print axioms LeanLab.BS2022GRH.RobinFinite406.finite_ratio

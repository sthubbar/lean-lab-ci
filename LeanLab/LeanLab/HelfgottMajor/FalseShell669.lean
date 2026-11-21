import LeanLab.HelfgottMajor.TailIntegral123

/-!
Audit of DecompF1605.shell_series_le_expTailIntegral against P0014 page 41, display 4.35.
The proposed shell majorant sums from zero and retains no lower cutoff T.
It cannot be bounded by the density tail as stated. No sealed statement is changed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.FalseShell669
open Real

/-- The unrestricted shell series comparison is false already at q one and T one hundred.
Its zeroth summand makes the left side at least 12800. The existing proved integral bound
puts the right side below 103 even after dropping the exponential decay. -/
theorem shell_series_le_expTailIntegral_false :
    ¬ ∀ (q : ℕ) (T : ℝ), q ≠ 0 → 100 ≤ T →
      6400 * ((q : ℝ) + 1) *
        (∑' n : ℕ, (((n : ℝ) ^ 2 + 1) * exp (-0.1598 * (n : ℝ)))) ≤
          TailIntegral123.expTailIntegral q T := by
  intro h
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * exp (-0.1598 * (n : ℝ))) := by
    simpa [Nat.cast_pow] using
      Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 0.1598)
  have h0 : Summable (fun n : ℕ => exp (-0.1598 * (n : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 0
      (by norm_num : (0 : ℝ) < 0.1598)
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2 + 1) * exp (-0.1598 * (n : ℝ))) := by
    simpa [add_mul] using h1.add h0
  have hterm := hs.le_tsum 0 (fun n _ => by positivity)
  simp only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
    mul_zero, exp_zero, one_mul] at hterm
  have ht := TailIntegral123.exp_integral_bound 1 100 le_rfl
  have ha : 1 ≤ (100 : ℝ) / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [pi_lt_four]
  have hb : (100 : ℝ) / (2 * π) ≤ 100 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pi_gt_three]
  have hl0 : 0 ≤ log ((100 : ℝ) / (2 * π)) := log_nonneg ha
  have hl : log ((100 : ℝ) / (2 * π)) ≤ 100 :=
    (log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have he : exp (-0.1598 * (100 : ℝ)) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  norm_num only [Nat.cast_one, one_mul] at ht
  have htail : TailIntegral123.expTailIntegral 1 100 ≤ 103 := by
    refine ht.trans ?_
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 1.0242))
      he (by positivity) (by positivity : (0 : ℝ) ≤ 1.0242 * 100)
    norm_num at hh
    linarith
  have hw := h 1 100 (by norm_num) le_rfl
  simp only [Nat.cast_one, show (6400 : ℝ) * (1 + 1) = 12800 by norm_num] at hw
  nlinarith

end LeanLab.HelfgottMajor.FalseShell669

#print axioms LeanLab.HelfgottMajor.FalseShell669.shell_series_le_expTailIntegral_false

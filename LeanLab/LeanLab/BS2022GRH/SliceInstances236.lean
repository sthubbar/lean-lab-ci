/- AI wrote the Lean code for CODEX task236.
Nonempty source domains for journal Theorem 7. Goldbach is open. -/
import LeanLab.BS2022GRH.SliceRanges236
namespace LeanLab.BS2022GRH.SliceRemainder236
open Real Finset Classical ChenThresholdGRH DecompC164c

/-- Every large input has a first multiplicative slice, journal display 26 p. 1236. -/
theorem zero_mem_slices (n : ℕ) (ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) :
    0 ∈ slices n ε₁ := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hnN : 0 < n := by exact_mod_cast hn0
  have hL := Lemma11C164.log_lower n hn
  rw [mem_slices_iff, Nat.cast_zero, log_y_div_z n hnN]
  exact div_pos (mul_pos (by norm_num) (by linarith)) (log_pos (by linarith))

/-- A kernel checked nonempty instance of the even source and bilinear domains,
journal pp. 1236, 1239 and 1240. No GRH or sieve witness is asserted. -/
theorem slice_domain_nonempty : ∃ n : ℕ, Even n ∧ exp (exp 10) ≤ (n : ℝ) ∧
    0 ∈ slices n (1 / 2) ∧ 25 ≤ w n (1 / 2) 0 ∧
    w n (1 / 2) 0 < min (U7153.yy n) ((1 + (1 / 2 : ℝ)) * w n (1 / 2) 0) ∧
    w n (1 / 2) 0 ≤ √((n : ℝ) / 2) := by
  obtain ⟨n, hev, hn⟩ := threshold_nonvacuous
  have hN : exp (exp 10) ≤ (n : ℝ) :=
    (exp_le_exp.mpr (exp_le_exp.mpr (by norm_num : (10 : ℝ) ≤ 13.375))).trans hn
  have hj := zero_mem_slices n (1 / 2) hN (by norm_num)
  have hr := slice_bilinear_basic_ranges n 0 (1 / 2) hN (by norm_num) (by norm_num) hj
  exact ⟨n, hev, hN, hj, hr.2.2.1, hr.2.2.2.1,
    slice_w_le_sqrt_half n 0 (1 / 2) hN (by norm_num) hj⟩

end LeanLab.BS2022GRH.SliceRemainder236
#print axioms LeanLab.BS2022GRH.SliceRemainder236.zero_mem_slices
#print axioms LeanLab.BS2022GRH.SliceRemainder236.slice_domain_nonempty

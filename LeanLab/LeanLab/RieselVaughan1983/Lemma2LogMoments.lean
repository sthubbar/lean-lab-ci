import LeanLab.RieselVaughan1983.Lemma2MomentZero

/-! Absolute convergence of the logarithmic moments used on pages 50 and 51.
AI wrote the Lean code. Binary Goldbach is OPEN. -/
namespace LeanLab.RieselVaughan1983.Lemma2
open Real
noncomputable section

def moment (k : ℕ) : ℝ := ∑' n : ℕ, g n * Real.log n ^ k

lemma log_le_root (n : ℕ) (hn : 0 < n) :
    Real.log n ≤ 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h := Real.add_one_le_exp (Real.log n / 3)
  rw [Real.rpow_def_of_pos hn0]
  have he : Real.exp (Real.log n / 3) = Real.exp (Real.log n * (1 / 3 : ℝ)) := by congr 1; ring
  rw [he] at h
  linarith

lemma log_sq_le_root (n : ℕ) (hn : 0 < n) :
    Real.log n ^ 2 ≤ 18 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h := Real.quadratic_le_exp_of_nonneg (x := Real.log n / 3) (by positivity)
  rw [Real.rpow_def_of_pos hn0]
  have he : Real.exp (Real.log n / 3) = Real.exp (Real.log n * (1 / 3 : ℝ)) := by congr 1; ring
  rw [he] at h
  nlinarith

lemma log_moment_summable_norm : Summable (fun n : ℕ => ‖g n * Real.log n‖) := by
  apply (mass_summable.mul_left 3).of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mass]
  · have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hl]
    have h := mul_le_mul_of_nonneg_left (log_le_root n hn) (abs_nonneg (g n))
    simpa only [mass, mul_left_comm, mul_assoc] using h

lemma log_sq_moment_summable_norm : Summable (fun n : ℕ => ‖g n * Real.log n ^ 2‖) := by
  apply (mass_summable.mul_left 18).of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mass]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Real.log n))]
    have h := mul_le_mul_of_nonneg_left (log_sq_le_root n hn) (abs_nonneg (g n))
    simpa only [mass, mul_left_comm, mul_assoc] using h

lemma moment_zero : moment 0 = 1 / Ctw := by
  simpa [moment, G] using G_zero

lemma moment_one_hasSum : HasSum (fun n : ℕ => g n * Real.log n) (moment 1) := by
  simpa [moment] using log_moment_summable_norm.of_norm.hasSum

lemma moment_two_hasSum : HasSum (fun n : ℕ => g n * Real.log n ^ 2) (moment 2) :=
  log_sq_moment_summable_norm.of_norm.hasSum

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.log_le_root
#print axioms LeanLab.RieselVaughan1983.Lemma2.log_sq_le_root
#print axioms LeanLab.RieselVaughan1983.Lemma2.log_moment_summable_norm
#print axioms LeanLab.RieselVaughan1983.Lemma2.log_sq_moment_summable_norm
#print axioms LeanLab.RieselVaughan1983.Lemma2.moment_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.moment_one_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.moment_two_hasSum

/-
AI wrote this Lean code. Binary Goldbach is open.
Pintz and Ruzsa 2003, P0026 page 176, proof of Lemma 4 before display 4.16.
-/
import LeanLab.PlattTrudgian2014.Mixed421

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- LEAF. P0026 page 176, each mixed integral in the binomial expansion is nonnegative.
This is the constant coefficient of a finite product with nonnegative coefficients.
There is no binomial comparison or exponential moment conclusion. -/
theorem mixed_power_integral_nonneg421 (L a b : ℕ) :
    0 ≤ ∫ x : ℝ in 0..1, ((G L x) ^ a * (star (G L x)) ^ b).re :=
  mixed_power_integral_proved421 L a b

/-- P0026 page 176, finite binomial identity for twice the real part. -/
theorem real_power_binomial421 (z : ℂ) (n : ℕ) :
    (2 : ℝ) ^ n * z.re ^ n =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (z ^ k * (star z) ^ (n - k)).re := by
  have hz : z + star z = ((2 * z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have h := congrArg Complex.re (add_pow z (star z) n)
  rw [hz] at h
  rw [← Complex.ofReal_pow, Complex.ofReal_re, mul_pow, Complex.re_sum] at h
  simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_mul, sub_zero, mul_comm] using h

/-- P0026 page 176, the integrated finite binomial identity before display 4.16. -/
theorem real_power_integral_binomial421 (L n : ℕ) :
    (2 : ℝ) ^ n * (∫ x : ℝ in 0..1, (G L x).re ^ n) =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) *
        (∫ x : ℝ in 0..1, ((G L x) ^ k * (star (G L x)) ^ (n - k)).re) := by
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [real_power_binomial421]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul]
  · intro k hk
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (n.choose k : ℝ) * ((G L x) ^ k * (star (G L x)) ^ (n - k)).re)).intervalIntegrable _ _

/-- P0026 page 176, the middle mixed power is the even norm power. -/
theorem mixed_power_middle421 (z : ℂ) (j : ℕ) :
    (z ^ j * (star z) ^ j).re = ‖z‖ ^ (2 * j) := by
  change (z ^ j * ((starRingEnd ℂ) z) ^ j).re = _
  rw [← mul_pow, Complex.mul_conj]
  simp only [Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
    Complex.ofReal_re, pow_mul]

/-- P0026 page 176, exact existing middle even moment comparison.
Mixed positivity is discharged by the finite tuple proof in Mixed421. -/
theorem even_middle_moment_decomposed421 (t : ℝ) (ht : 0 ≤ t) (L j : ℕ) :
    (Nat.centralBinom j : ℝ) * (∫ x : ℝ in 0..1, (t * ‖G L x‖) ^ (2 * j)) ≤
      (4 : ℝ) ^ j * (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) := by
  have hs := single_le_sum (s := range (2 * j + 1))
    (f := fun k => ((2 * j).choose k : ℝ) *
      (∫ x : ℝ in 0..1, ((G L x) ^ k * (star (G L x)) ^ (2 * j - k)).re))
    (fun k hk => mul_nonneg (Nat.cast_nonneg _) (mixed_power_integral_nonneg421 L k _))
    (show j ∈ range (2 * j + 1) by simp; omega)
  rw [← real_power_integral_binomial421] at hs
  have he : 2 * j - j = j := by omega
  simp_rw [he, mixed_power_middle421] at hs
  have hp : (2 : ℝ) ^ (2 * j) = (4 : ℝ) ^ j := by rw [pow_mul]; norm_num
  rw [hp] at hs
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hc : (Nat.centralBinom j : ℝ) = ((2 * j).choose j : ℝ) := rfl
  rw [hc]
  nlinarith [mul_le_mul_of_nonneg_left hs (pow_nonneg ht (2 * j))]

set_option format.width 240
#print axioms mixed_power_integral_nonneg421
#print axioms real_power_binomial421
#print axioms real_power_integral_binomial421
#print axioms mixed_power_middle421
#print axioms even_middle_moment_decomposed421

end LeanLab.PlattTrudgian2014

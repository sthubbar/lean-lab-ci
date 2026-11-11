/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 176, the nonnegative real moments in the estimate below display 4.17.
-/
import LeanLab.PlattTrudgian2014.Decomp421a

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- P0026 page 176, each real power has nonnegative integral.
Mixed power positivity is proved by the finite tuple bridge. -/
theorem real_power_integral_nonneg421 (t : ℝ) (ht : 0 ≤ t) (L n : ℕ) :
    0 ≤ ∫ x : ℝ in 0..1, (t * (G L x).re) ^ n := by
  have hs : 0 ≤ (2 : ℝ) ^ n * (∫ x : ℝ in 0..1, (G L x).re ^ n) := by
    rw [real_power_integral_binomial421]
    exact sum_nonneg fun k hk => mul_nonneg (Nat.cast_nonneg _)
      (mixed_power_integral_nonneg421 L k (n - k))
  have hi : 0 ≤ ∫ x : ℝ in 0..1, (G L x).re ^ n :=
    (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 2 ^ n)).mp hs
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul]
  exact mul_nonneg (pow_nonneg ht n) hi

/-- LEAF. P0026 page 174 display 4.11 and page 176 below display 4.17.
The integrated exponential series converges to the real exponential moment.
This convergence statement does not assert nonnegativity or any finite sum inequality. -/
theorem real_exp_integral_series421 (t : ℝ) (L : ℕ) :
    HasSum (fun n : ℕ => (∫ x : ℝ in 0..1, (t * (G L x).re) ^ n) / n.factorial)
      (∫ x : ℝ in 0..1, Real.exp (t * (G L x).re)) := by
  have hexp (u : ℝ) : HasSum (fun n : ℕ => u ^ n / n.factorial) (Real.exp u) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp u
  let A : ℝ := |t| * L
  have hA : 0 ≤ A := mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hmajor (x : ℝ) : |t * (G L x).re| ≤ A := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_G_le L x)) (abs_nonneg _)
  have hb (n : ℕ) (x : ℝ) : ‖(t * (G L x).re) ^ n / n.factorial‖ ≤ A ^ n / n.factorial := by
    have hf : |(n.factorial : ℝ)| = (n.factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg n.factorial)
    rw [Real.norm_eq_abs, abs_div, abs_pow, hf]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hmajor x) n)
      (Nat.cast_nonneg _)
  simp_rw [← intervalIntegral.integral_div]
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => A ^ n / (n.factorial : ℝ))
  · intro n
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (t * (G L x).re) ^ n / (n.factorial : ℝ))).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun x hx => hb n x
  · exact Filter.Eventually.of_forall fun x hx => (hexp A).summable
  · exact continuous_const.intervalIntegrable 0 1
  · exact Filter.Eventually.of_forall fun x hx => hexp (t * (G L x).re)

/-- P0026 page 176, exact existing finite even Taylor comparison.
Mixed power positivity and integrated Taylor convergence are proved above. -/
theorem finite_even_real_sum_decomposed421 (t : ℝ) (ht : 0 ≤ t) (L K : ℕ) :
    (∑ j ∈ range K,
      (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) / (2 * j).factorial) ≤
        ∫ x : ℝ in 0..1, Real.exp (t * (G L x).re) := by
  have hs := real_exp_integral_series421 t L
  rw [← hs.tsum_eq]
  have hi : Function.Injective (fun j : ℕ => 2 * j) := by
    intro a b h
    dsimp only at h
    omega
  calc
    _ = ∑ n ∈ (range K).image (fun j => 2 * j),
        (∫ x : ℝ in 0..1, (t * (G L x).re) ^ n) / n.factorial := by
      rw [sum_image (fun a ha b hb h => hi h)]
    _ ≤ _ := hs.summable.sum_le_tsum _ (fun n hn =>
      div_nonneg (real_power_integral_nonneg421 t ht L n) (Nat.cast_nonneg _))

set_option format.width 240
#print axioms real_power_integral_nonneg421
#print axioms real_exp_integral_series421
#print axioms finite_even_real_sum_decomposed421

end LeanLab.PlattTrudgian2014

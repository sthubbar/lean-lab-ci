/-
P0069, page 11, the coefficient energy in display 3.3.
A pointwise Cauchy Schwarz bound supplies an existing elementary OPEN leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165

namespace LeanLab.BHP1997.Decomp437b
open Classical Complex MeanSquareC165
open scoped BigOperators

/-- Page 11, elementary pointwise bound for the finite Dirichlet polynomial.
This is the exact mean_square_pointwise statement from the existing split.
It uses no cited mean value estimate and no spacing assumption. -/
theorem mean_square_pointwise (a : ℕ → ℂ) (c1 c2 F : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (hF : 0 < F) :
    ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ^ 2 ≤
      (((⌊c2 * F⌋₊ + 1 : ℕ) : ℝ) * energy a c1 c2 F) := by
  let S := (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  let f : ℕ → ℂ := fun n => a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t
  have hterm : ∀ n ∈ S, ‖f n‖ ^ 2 ≤ ‖a n‖ ^ 2 / (n : ℝ) := by
    intro n hn
    have hnlo := (Finset.mem_filter.mp hn).2.1
    have hnpos : 0 < n := by exact_mod_cast ((mul_pos hc1 hF).trans hnlo)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hden : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := by
      rw [← Real.rpow_mul_natCast hnR.le]
      norm_num
    dsimp [f]
    rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
    have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [hre, div_pow, mul_pow, hden]
    apply div_le_div_of_nonneg_right _ hnR.le
    have hc := pow_le_pow_left₀ (norm_nonneg (χ (n : ZMod q))) (χ.norm_le_one _) 2
    nlinarith [sq_nonneg ‖a n‖]
  have hnorm : ‖∑ n ∈ S, f n‖ ^ 2 ≤ (∑ n ∈ S, ‖f n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => ‖f n‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsum : (∑ n ∈ S, ‖f n‖ ^ 2) ≤ energy a c1 c2 F := Finset.sum_le_sum hterm
  have hcard : (S.card : ℝ) ≤ (⌊c2 * F⌋₊ + 1 : ℕ) := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Finset.card_range _)
  have hE : 0 ≤ energy a c1 c2 F := Finset.sum_nonneg (fun n hn => by positivity)
  exact (hnorm.trans hcs).trans (mul_le_mul hcard hsum
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))

end LeanLab.BHP1997.Decomp437b

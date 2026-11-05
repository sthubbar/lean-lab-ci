/-
P0093 page 162 Lemma 3. Close the former coefficient dependency.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357g

namespace LeanLab.Linnik1951

/-- P0093 page 162 equation 7.4. Parseval with the proved finite coefficient identity. -/
theorem parseval_second_moment_proved357 (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2) =
      ∑' u : ℕ, (primePowerCount111 u : ℝ) ^ 2 * Real.exp (-2 * u / N) := by
  calc
    _ = ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
          (fun α => primeFourier111 N α * powerFourier111 N α) i‖ ^ 2 :=
      fourier_parseval111 N hN
    _ = ∑' u : ℕ,
          ‖((primePowerCount111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ)‖ ^ 2 :=
      negative_modes_sum111 _ _ (fourier_coefficient_proved357 N hN)
    _ = _ := by
      apply tsum_congr
      intro u
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- P0093 page 162 Lemma 3. The proved Romanov moment and clean Parseval give the bound. -/
theorem lemma_three_proved357 : LemmaThree111 := by
  obtain ⟨C, hC, hprefix⟩ := romanov_second_moment111
  refine ⟨3 * C, by positivity, ?_⟩
  intro N hN
  rw [parseval_second_moment_proved357 N hN]
  have h := laplace_bound111 (fun u => (primePowerCount111 u : ℝ) ^ 2)
    C N hN hC.le (fun u => sq_nonneg _) hprefix
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith


end LeanLab.Linnik1951

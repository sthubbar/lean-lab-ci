/-
Elementary integrability inputs for the counting leaf of P0079.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp293b

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, display 12. The kernel decays quadratically away from zero. -/
theorem kernel_mul_sq_le293 (η α : ℝ) : kernel293 η α * α ^ 2 ≤ 1 / Real.pi ^ 2 := by
  by_cases hη : η = 0
  · simp [hη, kernel293]
    positivity
  by_cases hα : α = 0
  · simp [hα, kernel293]
    positivity
  have harg : Real.pi * η * α ≠ 0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero hη) hα
  unfold kernel293
  rw [Real.sinc_of_ne_zero harg]
  have heq : (η * (sin (Real.pi * η * α) / (Real.pi * η * α))) ^ 2 * α ^ 2 =
      sin (Real.pi * η * α) ^ 2 / Real.pi ^ 2 := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (sq_nonneg _)

/-- P0079 page 4, display 12. The kernel is bounded by an integrable Cauchy majorant. -/
theorem kernel_cauchy_le293 (η α : ℝ) :
    kernel293 η α ≤ (η ^ 2 + 1 / Real.pi ^ 2) * (1 + α ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [kernel_le293 η α, kernel_mul_sq_le293 η α]

/-- P0079 page 4, display 12. The continuous sine kernel is integrable on the real line. -/
theorem kernel_integrable293 (η : ℝ) : Integrable (kernel293 η) := by
  apply (integrable_inv_one_add_sq.const_mul (η ^ 2 + 1 / Real.pi ^ 2)).mono'
  · have hc : Continuous (kernel293 η) := by unfold kernel293; fun_prop
    exact hc.aestronglyMeasurable
  · exact Eventually.of_forall (fun α => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η α)] using kernel_cauchy_le293 η α)

/-- P0079 page 4, display 11. Multiplying the kernel by a character preserves integrability. -/
theorem kernel_character_integrable293 (η t : ℝ) :
    Integrable (fun α => character293 (t * α) * (kernel293 η α : ℂ)) := by
  have hk : Integrable (fun α => (kernel293 η α : ℂ)) :=
    (kernel_integrable293 η).ofReal
  apply hk.bdd_mul (c := 1)
  · have hc : Continuous (fun α : ℝ => character293 (t * α)) := by
      unfold character293
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Eventually.of_forall (fun α => (character_norm293 _).le)

/-- P0079 page 4, the prime sum is bounded uniformly in its frequency. -/
theorem primeSum_norm_le293 (ε X α : ℝ) :
    ‖primeSum293 ε X α‖ ≤
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), |log p| := by
  unfold primeSum293
  calc
    _ ≤ ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
      ‖(log p : ℂ) * character293 ((p : ℝ) * α)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, character_norm293, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- P0079 page 4, the powers sum is bounded by its number of terms. -/
theorem powerSum_norm_le293 (L α : ℝ) :
    ‖powerSum293 L α‖ ≤ ((Icc 1 ⌊L⌋₊).card : ℝ) := by
  unfold powerSum293
  calc
    _ ≤ ∑ m ∈ Icc 1 ⌊L⌋₊, ‖character293 (2 ^ m * α)‖ := norm_sum_le _ _
    _ = _ := by simp only [character_norm293, sum_const, nsmul_eq_mul, mul_one]

/-- P0079 page 4, definition of I and displays 11 to 12. All full-line
integrals in the counting argument are well-defined without an analytic hypothesis. -/
theorem integrand_integrable293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ) :
    Integrable (integrand293 s l1 l2 μ γ η ε X) := by
  let P := ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), |log p|
  let N : ℝ := ((Icc 1 ⌊cutoff293 s μ ε X⌋₊).card : ℝ)
  let g : ℝ → ℂ := fun α => primeSum293 ε X (l1 * α) * primeSum293 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) * character293 (γ * α)
  have hP : 0 ≤ P := sum_nonneg (fun _ _ => abs_nonneg _)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hprod : ∀ α : ℝ,
      ‖∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤ N ^ s := by
    intro α
    calc
      _ ≤ ∏ i : Fin s, ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ := norm_prod_le _ _
      _ ≤ ∏ _ : Fin s, N := prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => powerSum_norm_le293 _ _)
      _ = _ := by simp
  have hg : ∀ α : ℝ, ‖g α‖ ≤ (P * P) * N ^ s := by
    intro α
    dsimp [g]
    simp only [norm_mul, character_norm293, mul_one]
    exact mul_le_mul (mul_le_mul (primeSum_norm_le293 _ _ _) (primeSum_norm_le293 _ _ _)
      (norm_nonneg _) hP) (hprod α) (norm_nonneg _) (mul_nonneg hP hP)
  have hc : Continuous g := by
    dsimp [g]
    unfold primeSum293 powerSum293 character293
    fun_prop
  have hk : Integrable (fun α => (kernel293 η α : ℂ)) := (kernel_integrable293 η).ofReal
  exact hk.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hg)

end LeanLab.LZPowersOfTwo

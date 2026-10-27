import LeanLab.LanguascoPerelli1996.Kernel108

/-!
Finite Fourier sums underlying P0071 page 354 display 11.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.FiniteEnergy108
open Complex Real MeasureTheory

/-- LEAF. Page 354 display 11, expansion of the squared norm of a finite zero sum. -/
theorem norm_sq_expansion {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) (v : ℝ) :
    ((‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) *
        Complex.exp (Complex.I * (γ i - γ j) * v) := by
  classical
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal]
  calc
    _ = c i * starRingEnd ℂ (c j) *
        (Complex.exp (Complex.I * γ i * v) * Complex.exp (-Complex.I * γ j * v)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- LEAF. Page 354 display 11. Integration commutes with the finite pair sum. -/
theorem kernel_sum_integral {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    Integrable (fun v : ℝ => ∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) *
      (Complex.exp (Complex.I * (γ i - γ j) * v) * (Real.exp (-2 * |v|) : ℂ))) ∧
    (∫ v : ℝ, ∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) *
      (Complex.exp (Complex.I * (γ i - γ j) * v) * (Real.exp (-2 * |v|) : ℂ))) =
      ∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) * (w (γ i - γ j) : ℂ) := by
  classical
  have hij (i j : ι) : Integrable (fun v : ℝ => c i * starRingEnd ℂ (c j) *
      (Complex.exp (Complex.I * (γ i - γ j) * v) * (Real.exp (-2 * |v|) : ℂ))) :=
    by
      simpa only [Complex.ofReal_sub] using
        (Kernel108.integral_weight (γ i - γ j)).1.const_mul (c i * starRingEnd ℂ (c j))
  have his (i : ι) : Integrable (fun v : ℝ => ∑ j ∈ s, c i * starRingEnd ℂ (c j) *
      (Complex.exp (Complex.I * (γ i - γ j) * v) * (Real.exp (-2 * |v|) : ℂ))) :=
    integrable_finsetSum s (fun j _ => hij i j)
  refine ⟨integrable_finsetSum s (fun i _ => his i), ?_⟩
  rw [integral_finsetSum s (fun i _ => his i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (fun j _ => hij i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul]
  congr 1
  simpa only [Complex.ofReal_sub] using (Kernel108.integral_weight (γ i - γ j)).2

/-- LEAF. Page 354 display 11 for any finite exponential sum.
No GRH assumption is needed for this finite Fourier identity. -/
theorem finite_energy_identity {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    Integrable (fun v : ℝ => ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 *
      Real.exp (-2 * |v|)) ∧
    ((∫ v : ℝ, ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 *
      Real.exp (-2 * |v|) : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) * (w (γ i - γ j) : ℂ) := by
  classical
  have heq : (fun v : ℝ => ((‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 *
      Real.exp (-2 * |v|) : ℝ) : ℂ)) =
      (fun v : ℝ => ∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) *
        (Complex.exp (Complex.I * (γ i - γ j) * v) * (Real.exp (-2 * |v|) : ℂ))) := by
    funext v
    rw [Complex.ofReal_mul, norm_sq_expansion]
    simp only [Finset.sum_mul, mul_assoc]
  obtain ⟨hi, hint⟩ := kernel_sum_integral s c γ
  have hic : Integrable (fun v : ℝ => ((‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 *
      Real.exp (-2 * |v|) : ℝ) : ℂ)) := by rw [heq]; exact hi
  refine ⟨?_, ?_⟩
  · have hre := hic.re
    change Integrable (fun v : ℝ => Complex.re ((‖∑ i ∈ s,
      c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 * Real.exp (-2 * |v|) : ℝ) : ℂ)) at hre
    simpa only [Complex.ofReal_re] using hre
  · rw [← integral_complex_ofReal, heq]
    exact hint

end LeanLab.LanguascoPerelli1996.FiniteEnergy108

/-
P0079 page 10, full continuous model expansion behind display 36.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp396a
import LeanLab.LZPowersOfTwo.ModelFourier353

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, display 32. The continuous prime model is bounded
by the length of its defining interval. -/
theorem continuousPrime_norm_le396 (ε X α : ℝ) :
    ‖continuousPrime353 ε X α‖ ≤ |X - ε * X| := by
  simpa only [continuousPrime353, one_mul] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := ε * X) (b := X) (C := 1)
    (f := fun t : ℝ => character293 (t * α)) (fun t ht => (character_norm293 _).le)

/-- P0079 page 10, definition of J after display 36.
Each full continuous pair transform is absolutely integrable. -/
theorem continuous_pair_integrable396 (ε X l1 l2 u η : ℝ) :
    Integrable (fun α : ℝ => continuousPrime353 ε X (l1 * α) *
      continuousPrime353 ε X (l2 * α) * character293 (u * α) * (kernel293 η α : ℂ)) := by
  have hc : Continuous (fun α : ℝ => continuousPrime353 ε X (l1 * α) *
      continuousPrime353 ε X (l2 * α) * character293 (u * α)) := by
    apply Continuous.mul
    · exact ((continuousPrime_continuous396 ε X).comp (by fun_prop)).mul
        ((continuousPrime_continuous396 ε X).comp (by fun_prop))
    · unfold character293
      fun_prop
  apply ((kernel_integrable293 η).ofReal).bdd_mul (c := |X - ε * X| ^ 2)
    hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro α
  simp only [norm_mul, character_norm293, mul_one, pow_two]
  exact mul_le_mul (continuousPrime_norm_le396 ε X (l1 * α))
    (continuousPrime_norm_le396 ε X (l2 * α)) (norm_nonneg _) (abs_nonneg _)

/-- P0079 page 10, display 36. Expanding the power sums expresses the
continuous model as a finite sum of pair transforms with shifted phases. -/
theorem majorModel_expansion396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ)
    (γ η ε X α : ℝ) :
    majorModel353 s l1 l2 μ γ η ε X α =
      ∑ m ∈ Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊cutoff293 s μ ε X⌋₊),
        continuousPrime353 ε X (l1 * α) * continuousPrime353 ε X (l2 * α) *
          character293 (((∑ i : Fin s, μ i * 2 ^ m i) + γ) * α) * (kernel293 η α : ℂ) := by
  classical
  unfold majorModel353 powerSum293
  simp_rw [Finset.prod_univ_sum, Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro m hm
  rw [← character_sum293]
  have he : (∑ i : Fin s, (2 : ℝ) ^ m i * (μ i * α)) + γ * α =
      ((∑ i : Fin s, μ i * 2 ^ m i) + γ) * α := by
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
  rw [← he, character_add293]
  ring

/-- P0079 page 10, display 36 and the definition of J after it.
The full model is exactly a finite sum of real double-box tent integrals. -/
theorem full_model_transform396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ)
    (γ η ε X : ℝ) (hbox : ε * X ≤ X) (hη : 0 < η) :
    (∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α).re =
      ∑ m ∈ Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊cutoff293 s μ ε X⌋₊),
        ∫ v in Set.Icc (ε * X) X, ∫ t in Set.Icc (ε * X) X,
          max 0 (η - |l1 * t + l2 * v + ((∑ i : Fin s, μ i * 2 ^ m i) + γ)|) := by
  classical
  simp_rw [majorModel_expansion396]
  rw [integral_finsetSum _ (fun m hm => continuous_pair_integrable396 ε X l1 l2 _ η)]
  simp only [Complex.re_sum]
  apply sum_congr rfl
  intro m hm
  have H := congrArg Complex.re
    (continuous_pair_transform353 (ε * X) X l2 l1 ((∑ i : Fin s, μ i * 2 ^ m i) + γ) η hη)
  simpa only [continuousPrime353, intervalIntegral.integral_of_le hbox,
    ← integral_Icc_eq_integral_Ioc, integral_complex_ofReal, Complex.ofReal_re, mul_comm, add_comm] using H

end LeanLab.LZPowersOfTwo

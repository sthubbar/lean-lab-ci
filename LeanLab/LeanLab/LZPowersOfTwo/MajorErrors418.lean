/-
The exact J2 and J3 decomposition of P0079 page 9, display 33.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp353b

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, display 32. The continuous prime model is continuous in its frequency. -/
theorem continuousPrime_continuous418 (ε X : ℝ) : Continuous (continuousPrime353 ε X) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry character293
  fun_prop

/-- P0079 page 9, display 33, J2 has only the first prime discrepancy. -/
def majorError2418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  (primeSum293 ε X (l1 * α) - continuousPrime353 ε X (l1 * α)) *
    continuousPrime353 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

/-- P0079 page 9, display 33, J3 has only the second prime discrepancy. -/
def majorError3418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  primeSum293 ε X (l1 * α) *
    (primeSum293 ε X (l2 * α) - continuousPrime353 ε X (l2 * α)) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

/-- P0079 page 9, display 33. A continuous function is integrable on the compact major arc. -/
theorem continuous_major_integrable418 (f : ℝ → ℂ) (hf : Continuous f) (X : ℝ) :
    IntegrableOn f (major293 X) := by
  have heq : major293 X = Set.Icc (-(X ^ (1 / 3 : ℝ) / X)) (X ^ (1 / 3 : ℝ) / X) := by
    ext α
    change |α| ≤ X ^ (1 / 3 : ℝ) / X ↔ _
    exact abs_le
  rw [heq]
  exact hf.integrableOn_Icc

/-- P0079 page 9, display 33. The model and both individual error integrands
are integrable on the major arc without any prime distribution input. -/
theorem major_errors_integrable418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ) :
    IntegrableOn (majorModel353 s l1 l2 μ γ η ε X) (major293 X) ∧
    IntegrableOn (majorError2418 s l1 l2 μ γ η ε X) (major293 X) ∧
    IntegrableOn (majorError3418 s l1 l2 μ γ η ε X) (major293 X) := by
  have hT (l : ℝ) : Continuous (fun α : ℝ => continuousPrime353 ε X (l * α)) :=
    (continuousPrime_continuous418 ε X).comp (continuous_const.mul continuous_id)
  have hS (l : ℝ) : Continuous (fun α : ℝ => primeSum293 ε X (l * α)) := by
    unfold primeSum293 character293
    fun_prop
  have hG : Continuous (fun α : ℝ => ∏ i : Fin s,
      powerSum293 (cutoff293 s μ ε X) (μ i * α)) := by
    unfold powerSum293 character293
    fun_prop
  have he : Continuous (fun α : ℝ => character293 (γ * α)) := by
    unfold character293
    fun_prop
  have hk : Continuous (fun α : ℝ => (kernel293 η α : ℂ)) := by
    unfold kernel293
    fun_prop
  refine ⟨continuous_major_integrable418 _ ?_ X,
    continuous_major_integrable418 _ ?_ X, continuous_major_integrable418 _ ?_ X⟩
  · exact ((((hT l1).mul (hT l2)).mul hG).mul he).mul hk
  · exact (((((hS l1).sub (hT l1)).mul (hT l2)).mul hG).mul he).mul hk
  · exact ((((hS l1).mul ((hS l2).sub (hT l2))).mul hG).mul he).mul hk

/-- P0079 page 9, display 33. The prime-model integral difference is exactly J2 plus J3. -/
theorem major_errors_split418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ) :
    (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
      (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α) =
    (∫ α in major293 X, majorError2418 s l1 l2 μ γ η ε X α) +
      (∫ α in major293 X, majorError3418 s l1 l2 μ γ η ε X α) := by
  obtain ⟨hm, h2, h3⟩ := major_errors_integrable418 s l1 l2 μ γ η ε X
  rw [← integral_sub (integrand_integrable293 s l1 l2 μ γ η ε X).integrableOn hm,
    ← integral_add h2 h3]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro α
  unfold integrand293 majorModel353 majorError2418 majorError3418
  ring

end LeanLab.LZPowersOfTwo

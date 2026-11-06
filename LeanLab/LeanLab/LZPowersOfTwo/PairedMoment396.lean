/-
P0079 pages 6 to 7 and 11, paired moments and the elementary reduction.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.MinorProduct396

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 6, Lemma 4. The paired prime-power second moment integrand. -/
def pairedMoment396 (l m L η ε X α : ℝ) : ℝ :=
  ‖primeSum293 ε X (l * α) * powerSum293 L (m * α)‖ ^ 2 * kernel293 η α

/-- P0079 page 6, Lemma 4. The finite paired second moment is integrable. -/
theorem pairedMoment_integrable396 (l m L η ε X : ℝ) :
    Integrable (pairedMoment396 l m L η ε X) := by
  let P := ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), |log p|
  let N : ℝ := ((Icc 1 ⌊L⌋₊).card : ℝ)
  have hP : 0 ≤ P := sum_nonneg (fun _ _ => abs_nonneg _)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hc : Continuous (fun α : ℝ =>
      ‖primeSum293 ε X (l * α) * powerSum293 L (m * α)‖ ^ 2) := by
    unfold primeSum293 powerSum293 character293
    fun_prop
  apply (kernel_integrable293 η).bdd_mul (c := (P * N) ^ 2) hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro α
  change |‖primeSum293 ε X (l * α) * powerSum293 L (m * α)‖ ^ 2| ≤ (P * N) ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul]
  exact mul_le_mul (primeSum_norm_le293 ε X (l * α))
    (powerSum_norm_le293 L (m * α)) (norm_nonneg _) hP

/-- P0079 page 11, display 41. CONDITIONAL ON the two displayed moment
bounds in its hypotheses. The proof is only weighted Cauchy Schwarz and
contains no number-theoretic estimate for either paired moment. -/
theorem paired_integral_bound396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ)
    (γ η ε X B a b W : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (hs : 2 ≤ s) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b)
    (hG : ∀ α ∈ E, ∀ i : Fin s, ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤ B)
    (hm1 : (∫ α : ℝ, pairedMoment396 l1 (μ 0) (cutoff293 s μ ε X) η ε X α) ≤ a ^ 2 * W)
    (hm2 : (∫ α : ℝ, pairedMoment396 l2 (μ 1) (cutoff293 s μ ε X) η ε X α) ≤ b ^ 2 * W) :
    ‖∫ α in E, integrand293 s l1 l2 μ γ η ε X α‖ ≤ B ^ (s - 2) * a * b * W := by
  let f1 := pairedMoment396 l1 (μ 0) (cutoff293 s μ ε X) η ε X
  let f2 := pairedMoment396 l2 (μ 1) (cutoff293 s μ ε X) η ε X
  have hi1 : Integrable f1 := pairedMoment_integrable396 _ _ _ _ _ _
  have hi2 : Integrable f2 := pairedMoment_integrable396 _ _ _ _ _ _
  have hJ1 : (∫ α in E, f1 α) ≤ a ^ 2 * W :=
    (setIntegral_le_integral hi1 (Eventually.of_forall (fun α =>
      mul_nonneg (sq_nonneg _) (kernel_nonneg293 η α)))).trans hm1
  have hJ2 : (∫ α in E, f2 α) ≤ b ^ 2 * W :=
    (setIntegral_le_integral hi2 (Eventually.of_forall (fun α =>
      mul_nonneg (sq_nonneg _) (kernel_nonneg293 η α)))).trans hm2
  have hpoint (α : ℝ) (hα : α ∈ E) :
      ‖integrand293 s l1 l2 μ γ η ε X α‖ ≤
        B ^ (s - 2) / 2 * ((b / a) * f1 α + (a / b) * f2 α) := by
    let u := ‖primeSum293 ε X (l1 * α) * powerSum293 (cutoff293 s μ ε X) (μ 0 * α)‖
    let v := ‖primeSum293 ε X (l2 * α) * powerSum293 (cutoff293 s μ ε X) (μ 1 * α)‖
    have he : ((b / a) * u ^ 2 + (a / b) * v ^ 2) / 2 - u * v =
        (b * u - a * v) ^ 2 / (2 * a * b) := by field_simp; ring
    have hy : u * v ≤ ((b / a) * u ^ 2 + (a / b) * v ^ 2) / 2 := by
      have H := div_nonneg (sq_nonneg (b * u - a * v)) (by positivity : 0 ≤ 2 * a * b)
      linarith only [he, H]
    calc
      _ ≤ B ^ (s - 2) * u * v * kernel293 η α :=
        integrand_paired_bound396 s l1 l2 μ γ η ε X α B hs hB (hG α hα)
      _ ≤ B ^ (s - 2) * (((b / a) * u ^ 2 + (a / b) * v ^ 2) / 2) * kernel293 η α :=
        by
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hy (pow_nonneg hB (s - 2))) (kernel_nonneg293 η α))
      _ = _ := by dsimp [f1, f2, pairedMoment396, u, v]; ring
  calc
    _ ≤ ∫ α in E, ‖integrand293 s l1 l2 μ γ η ε X α‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ α in E, B ^ (s - 2) / 2 * ((b / a) * f1 α + (a / b) * f2 α) := by
      apply setIntegral_mono_on (integrand_integrable293 s l1 l2 μ γ η ε X).norm.integrableOn
        (((hi1.const_mul _).add (hi2.const_mul _)).const_mul _).integrableOn hE
      exact hpoint
    _ = B ^ (s - 2) / 2 * ((b / a) * (∫ α in E, f1 α) +
        (a / b) * (∫ α in E, f2 α)) := by
      rw [integral_const_mul, integral_add (hi1.integrableOn.const_mul _) (hi2.integrableOn.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ B ^ (s - 2) / 2 * ((b / a) * (a ^ 2 * W) + (a / b) * (b ^ 2 * W)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hJ1 (by positivity))
        (mul_le_mul_of_nonneg_left hJ2 (by positivity))) (by positivity)
    _ = _ := by field_simp; ring

/-- P0079 page 6, the constant in Lemma 4. The printed C rounds
strictly above twice the Bombieri Davenport coefficient times one plus
the printed Khalfalah Pintz upper bound. -/
theorem bigC_rounding396 :
    2 * (3.9171 : ℝ) * (1 + 0.2792521041) < bigC := by
  norm_num [bigC]

end LeanLab.LZPowersOfTwo

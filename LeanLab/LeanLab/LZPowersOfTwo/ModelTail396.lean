/-
P0079 page 10, display 36, continuous model truncation.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.ContinuousDecay396
import LeanLab.LZPowersOfTwo.TailIntegral396
import LeanLab.LZPowersOfTwo.ArcGeometry353

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, display 36. The full continuous model is integrable
because its finite expansion has integrable pair-transform terms. -/
theorem majorModel_integrable396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ) :
    Integrable (majorModel353 s l1 l2 μ γ η ε X) := by
  have H := integrable_finsetSum
    (Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊cutoff293 s μ ε X⌋₊))
    (fun m hm => continuous_pair_integrable396 ε X l1 l2 ((∑ i : Fin s, μ i * 2 ^ m i) + γ) η)
  apply H.congr
  exact Eventually.of_forall (fun α => (majorModel_expansion396 s l1 l2 μ γ η ε X α).symm)

/-- P0079 page 10, display 36, from display 32 and the kernel bound.
The continuous model has an explicit inverse-square bound away from zero. -/
theorem majorModel_decay396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ)
    (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hα : α ≠ 0) (hL : 0 ≤ cutoff293 s μ ε X) :
    ‖majorModel353 s l1 l2 μ γ η ε X α‖ ≤
      (η ^ 2 / (Real.pi ^ 2 * |l1 * l2|) * (cutoff293 s μ ε X) ^ s) / α ^ 2 := by
  have hG : ‖∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤
      (cutoff293 s μ ε X) ^ s := by
    calc
      _ ≤ ∏ i : Fin s, ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ := norm_prod_le _ _
      _ ≤ ∏ _ : Fin s, cutoff293 s μ ε X := by
        apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i hi
        refine (powerSum_norm_le293 _ _).trans ?_
        simpa using Nat.floor_le hL
      _ = _ := by simp
  have hT1 := continuousPrime_decay396 ε X (l1 * α) (mul_ne_zero hl1 hα)
  have hT2 := continuousPrime_decay396 ε X (l2 * α) (mul_ne_zero hl2 hα)
  simp only [majorModel353, norm_mul, character_norm293, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η α)]
  calc
    _ ≤ ((1 / (Real.pi * |l1 * α|)) * (1 / (Real.pi * |l2 * α|))) *
        (cutoff293 s μ ε X) ^ s * η ^ 2 := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul hT1 hT2 (norm_nonneg _) (by positivity)) hG
          (norm_nonneg _) (by positivity))
        (kernel_le293 η α) (kernel_nonneg293 η α) (by positivity)
    _ = _ := by rw [abs_mul, abs_mul, abs_mul, ← sq_abs α]; ring

/-- P0079 page 10, display 36. Removing the complement of a centered
interval from the full continuous model has an explicit reciprocal-cutoff error. -/
theorem majorModel_tail_bound396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X a : ℝ)
    (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (ha : 0 < a) (hL : 0 ≤ cutoff293 s μ ε X) :
    ‖(∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α) -
        (∫ α in {α : ℝ | |α| ≤ a}, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
      2 * (η ^ 2 / (Real.pi ^ 2 * |l1 * l2|) * (cutoff293 s μ ε X) ^ s) / a := by
  have hm : MeasurableSet {α : ℝ | |α| ≤ a} := by measurability
  rw [← setIntegral_compl hm (majorModel_integrable396 s l1 l2 μ γ η ε X)]
  calc
    _ ≤ ∫ α in {α : ℝ | |α| ≤ a}ᶜ, ‖majorModel353 s l1 l2 μ γ η ε X α‖ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by
      have H := inverse_square_tail_bound396
        (fun α => ‖majorModel353 s l1 l2 μ γ η ε X α‖)
        (majorModel_integrable396 s l1 l2 μ γ η ε X).norm a
        (η ^ 2 / (Real.pi ^ 2 * |l1 * l2|) * (cutoff293 s μ ε X) ^ s) ha (by positivity)
        (fun α hα => majorModel_decay396 s l1 l2 μ γ η ε X α hl1 hl2
          (by intro he; simp [he] at hα; linarith) hL)
      simpa only [Set.compl_setOf, not_le] using H

/-- P0079 page 10, display 36. The exact major_model_tail375 statement
follows from the explicit reciprocal-cutoff bound and X to the one third
tending to infinity. No OPEN estimate is used. -/
theorem major_model_tail396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  let C := 2 * η ^ 2 / (Real.pi ^ 2 * |l1 * l2|)
  intro δ hδ
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually
    (eventually_ge_atTop (C / δ)), eventually_ge_atTop (1 : ℝ),
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (0 : ℝ))]
    with X hpow hX hL
  have hX0 : 0 < X := by linarith
  have hP : 0 < X ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hratio : C / X ^ (1 / 3 : ℝ) ≤ δ := by
    apply (div_le_iff₀ hP).mpr
    have H := (div_le_iff₀ hδ).mp hpow
    nlinarith only [H]
  calc
    _ ≤ 2 * (η ^ 2 / (Real.pi ^ 2 * |l1 * l2|) * (cutoff293 s μ ε X) ^ s) /
        (X ^ (1 / 3 : ℝ) / X) :=
      majorModel_tail_bound396 s l1 l2 μ γ η ε X _ (by linarith) (by linarith)
        (by positivity) hL
    _ = (C / X ^ (1 / 3 : ℝ)) * X * (cutoff293 s μ ε X) ^ s := by dsimp [C]; simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hratio hX0.le) (pow_nonneg hL _)

end LeanLab.LZPowersOfTwo

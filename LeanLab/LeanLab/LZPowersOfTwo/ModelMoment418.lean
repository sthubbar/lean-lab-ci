/-
The continuous second moment needed in P0079 page 9, the J2 estimate.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.RiemannFirst418
import LeanLab.LZPowersOfTwo.ContinuousDecay396
import LeanLab.LZPowersOfTwo.TailIntegral396

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, display 32. Squaring the inverse-frequency bound
controls the continuous model times frequency squared. -/
theorem continuousPrime_square_decay418 (ε X l α : ℝ) (hl : l ≠ 0) :
    ‖continuousPrime353 ε X (l * α)‖ ^ 2 * α ^ 2 ≤ (1 / (Real.pi * |l|)) ^ 2 := by
  by_cases hα : α = 0
  · simp only [hα, zero_pow (by decide : 2 ≠ 0), mul_zero]
    positivity
  have H := continuousPrime_decay396 ε X (l * α) (mul_ne_zero hl hα)
  rw [abs_mul, show 1 / (Real.pi * (|l| * |α|)) = (1 / (Real.pi * |l|)) / |α| by ring] at H
  have H' := (le_div_iff₀ (abs_pos.mpr hα)).mp H
  have Hsq := pow_le_pow_left₀ (by positivity) H' 2
  simpa only [mul_pow, sq_abs] using Hsq

/-- P0079 page 9, display 32, the continuous second moment in the J2 estimate.
The squared continuous model is integrable for every nonzero coefficient. -/
theorem continuousPrime_square_integrable418 (ε X l : ℝ) (hl : l ≠ 0) :
    Integrable (fun α : ℝ => ‖continuousPrime353 ε X (l * α)‖ ^ 2) := by
  let A := |X - ε * X|
  let K := (1 / (Real.pi * |l|)) ^ 2
  have hc : Continuous (fun α : ℝ => ‖continuousPrime353 ε X (l * α)‖ ^ 2) :=
    ((continuousPrime_continuous418 ε X).comp (continuous_const.mul continuous_id)).norm.pow 2
  apply (integrable_inv_one_add_sq.const_mul (A ^ 2 + K)).mono' hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro α
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1 + α ^ 2)).mpr
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (continuousPrime_norm_le418 ε X (l * α)) 2
  have h1 := continuousPrime_square_decay418 ε X l α hl
  change ‖continuousPrime353 ε X (l * α)‖ ^ 2 ≤ A ^ 2 at h0
  change ‖continuousPrime353 ε X (l * α)‖ ^ 2 * α ^ 2 ≤ K at h1
  nlinarith only [h0, h1]

/-- P0079 page 9, display 32 and the written J2 estimate after display 35.
The full continuous second moment is bounded by an explicit constant times X. -/
theorem continuousPrime_second_moment418 (ε X l : ℝ) (hl : l ≠ 0)
    (hX : 0 < X) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ α : ℝ, ‖continuousPrime353 ε X (l * α)‖ ^ 2) ≤
      (2 + 2 * (1 / (Real.pi * |l|)) ^ 2) * X := by
  let f : ℝ → ℝ := fun α => ‖continuousPrime353 ε X (l * α)‖ ^ 2
  let a := 1 / X
  let K := (1 / (Real.pi * |l|)) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hi : Integrable f := continuousPrime_square_integrable418 ε X l hl
  have hcenter : (∫ α in Set.Icc (-a) a, f α) ≤ 2 * X := by
    have hbound (α : ℝ) : f α ≤ X ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      apply (continuousPrime_norm_le418 ε X (l * α)).trans
      rw [abs_of_nonneg (by nlinarith : 0 ≤ X - ε * X)]
      nlinarith
    calc
      _ ≤ ∫ α in Set.Icc (-a) a, (X ^ 2 : ℝ) := by
        apply setIntegral_mono_on hi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
        exact fun α _ => hbound α
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc,
          max_eq_left (by linarith : 0 ≤ a - -a)]
        dsimp [a]
        field_simp
        norm_num
  have htail : (∫ α in {α : ℝ | a < |α|}, f α) ≤ 2 * K * X := by
    have H := inverse_square_tail_bound396 f hi a K ha (sq_nonneg _) (by
      intro α hα
      have hα0 : α ≠ 0 := by intro h; simp [h] at hα; linarith
      apply (le_div_iff₀ (sq_pos_of_ne_zero hα0)).mpr
      exact continuousPrime_square_decay418 ε X l α hl)
    convert H using 1
    dsimp [a]
    field_simp
  have hcomp : (Set.Icc (-a) a)ᶜ = {α : ℝ | a < |α|} := by
    ext α
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, ← abs_le, not_le]
  have H := integral_add_compl (s := Set.Icc (-a) a) measurableSet_Icc hi
  rw [hcomp] at H
  change (∫ α : ℝ, f α) ≤ (2 + 2 * K) * X
  rw [← H]
  nlinarith only [hcenter, htail]

end LeanLab.LZPowersOfTwo

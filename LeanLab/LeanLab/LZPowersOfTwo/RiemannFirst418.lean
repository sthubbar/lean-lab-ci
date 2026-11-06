/-
P0079 page 9, the elementary U minus T contribution to J2.
This reuses the integer approximation proved in task396 for the other factor.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.IntegerApprox396
import LeanLab.LZPowersOfTwo.ArcGeometry353
import LeanLab.LZPowersOfTwo.MajorErrors418

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, the J2 proof after display 35. Only its first factor is the integer sum U. -/
def discreteFirstModel418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  discretePrime396 ε X (l1 * α) * continuousPrime353 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

/-- P0079 page 9, display 32. The continuous prime model is bounded by its interval length. -/
theorem continuousPrime_norm_le418 (ε X α : ℝ) :
    ‖continuousPrime353 ε X α‖ ≤ |X - ε * X| := by
  exact (intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ => (character_norm293 (t * α)).le)).trans_eq (one_mul _)

/-- P0079 page 9, the analogous J2 estimate after display 35.
The elementary quadrature contribution has an explicit uniform major-arc bound. -/
theorem first_riemann_pointwise418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ)
    (γ η ε X α : ℝ) (hX : 1 ≤ X) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hL : 0 ≤ cutoff293 s μ ε X) (hα : α ∈ major293 X) :
    ‖discreteFirstModel418 s l1 l2 μ γ η ε X α - majorModel353 s l1 l2 μ γ η ε X α‖ ≤
      X * (2 + Real.pi * |l1| * X ^ (1 / 3 : ℝ)) *
        (cutoff293 s μ ε X) ^ s * η ^ 2 := by
  have hX0 : 0 < X := by linarith
  have ha : 0 ≤ ε * X := mul_nonneg hε hX0.le
  have hab : ε * X ≤ X := by nlinarith
  have hlen : 0 ≤ X - ε * X := sub_nonneg.mpr hab
  have hscaled : |α| * X ≤ X ^ (1 / 3 : ℝ) :=
    (le_div_iff₀ hX0).mp hα
  have herr := discretePrime_sub_continuous396 ε X (l1 * α) ha hab
  have herr' : ‖discretePrime396 ε X (l1 * α) - continuousPrime353 ε X (l1 * α)‖ ≤
      2 + Real.pi * |l1| * X ^ (1 / 3 : ℝ) := by
    apply herr.trans
    apply add_le_add le_rfl
    calc
      _ ≤ Real.pi * |l1 * α| * X := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = Real.pi * |l1| * (|α| * X) := by rw [abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (by positivity)
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
  have he : discreteFirstModel418 s l1 l2 μ γ η ε X α - majorModel353 s l1 l2 μ γ η ε X α =
      (discretePrime396 ε X (l1 * α) - continuousPrime353 ε X (l1 * α)) *
        continuousPrime353 ε X (l2 * α) *
        (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
        character293 (γ * α) * kernel293 η α := by
    unfold discreteFirstModel418 majorModel353
    ring
  rw [he]
  simp only [norm_mul, character_norm293, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (kernel_nonneg293 η α)]
  have hT : ‖continuousPrime353 ε X (l2 * α)‖ ≤ X := by
    apply (continuousPrime_norm_le418 ε X (l2 * α)).trans
    rw [abs_of_nonneg hlen]
    linarith
  have H := mul_le_mul
    (mul_le_mul (mul_le_mul herr' hT (norm_nonneg _) (by positivity))
      hG (norm_nonneg _) (by positivity))
    (kernel_le293 η α) (kernel_nonneg293 η α) (by positivity)
  convert H using 1 <;> ring

/-- P0079 page 9, the quadrature contribution in the written J2 proof.
The first-prime integer versus continuous contribution has an elementary proof
from the proved integer approximation and the continuous interval-length bound. -/
theorem major_first_riemann418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, discreteFirstModel418 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε (show 0 < l1 by linarith)]
  let K := 2 * (2 + Real.pi * |l1|) * η ^ 2
  intro δ hδ
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually
    (eventually_ge_atTop (K / δ)), eventually_ge_atTop (1 : ℝ),
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (0 : ℝ))]
    with X hpow hX hL
  let P := X ^ (1 / 3 : ℝ)
  let a := P / X
  have hX0 : 0 < X := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hX (by norm_num)
  have hP0 : 0 < P := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hP3 : P ^ 3 = X := by
    dsimp [P]
    rw [← Real.rpow_mul_natCast hX0.le]
    norm_num
  have hK : K ≤ δ * P := by
    have H := (div_le_iff₀ hδ).mp hpow
    nlinarith only [H]
  have hmajor : major293 X = Set.Icc (-a) a := by
    ext α
    simp only [major293, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
    rfl
  have hT : Continuous (continuousPrime353 ε X) := by
    unfold continuousPrime353
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold Function.uncurry character293
    fun_prop
  have hTC := hT.comp (show Continuous (fun α : ℝ => l2 * α) by fun_prop)
  have hTC1 := hT.comp (show Continuous (fun α : ℝ => l1 * α) by fun_prop)
  have hdis : Continuous (discreteFirstModel418 s l1 l2 μ γ η ε X) := by
    unfold discreteFirstModel418 discretePrime396 powerSum293 character293 kernel293
    fun_prop
  have hmix : Continuous (majorModel353 s l1 l2 μ γ η ε X) := by
    unfold majorModel353 powerSum293 character293 kernel293
    fun_prop
  have hdisI : IntegrableOn (discreteFirstModel418 s l1 l2 μ γ η ε X) (major293 X) := by
    rw [hmajor]
    exact hdis.integrableOn_Icc
  have hmixI : IntegrableOn (majorModel353 s l1 l2 μ γ η ε X) (major293 X) := by
    rw [hmajor]
    exact hmix.integrableOn_Icc
  have hpoint (α : ℝ) (hα : α ∈ major293 X) :
      ‖discreteFirstModel418 s l1 l2 μ γ η ε X α - majorModel353 s l1 l2 μ γ η ε X α‖ ≤
        X * ((2 + Real.pi * |l1|) * P) * (cutoff293 s μ ε X) ^ s * η ^ 2 := by
    apply (first_riemann_pointwise418 s l1 l2 μ γ η ε X α hX hε.le hε1.le hL hα).trans
    have hi : 2 + Real.pi * |l1| * P ≤ (2 + Real.pi * |l1|) * P := by nlinarith only [hP1]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by positivity))
        (pow_nonneg hL _)) (sq_nonneg η)
  calc
    _ = ‖∫ α in major293 X, discreteFirstModel418 s l1 l2 μ γ η ε X α -
        majorModel353 s l1 l2 μ γ η ε X α‖ := by rw [integral_sub hdisI hmixI]
    _ ≤ (X * ((2 + Real.pi * |l1|) * P) * (cutoff293 s μ ε X) ^ s * η ^ 2) *
        volume.real (major293 X) :=
      norm_setIntegral_le_of_norm_le_const (by rw [hmajor]; exact isCompact_Icc.measure_lt_top) hpoint
    _ = K * P ^ 2 * (cutoff293 s μ ε X) ^ s := by
      rw [hmajor, Real.volume_real_Icc, max_eq_left (by linarith : 0 ≤ a - -a)]
      dsimp [K, a]
      field_simp
      ring
    _ ≤ δ * X * (cutoff293 s μ ε X) ^ s := by
      have H := mul_le_mul_of_nonneg_right hK (sq_nonneg P)
      have he : δ * P * P ^ 2 = δ * X := by
        calc
          _ = δ * P ^ 3 := by ring
          _ = _ := by rw [hP3]
      rw [he] at H
      exact mul_le_mul_of_nonneg_right H (pow_nonneg hL _)

end LeanLab.LZPowersOfTwo

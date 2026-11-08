import LeanLab.ExceptionalSet.Decomp464g
import Mathlib.MeasureTheory.Function.Floor

/-!
P0082 page 356, local absolute sampling control from a reproducing convolution.
The real floor reduces every shift to one common compact majorant.
Only finite sums and integrable majorants are exchanged.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464h

open Real MeasureTheory

/-- P0082 page 356, local sampling auxiliary for Lemma 1.
A reproduced L1 kernel inherits local absolute translate summability from the reproducer.
The proof bounds every finite sum by one L1 mass times a summable compact majorant. -/
theorem convolution_translate_norm (K H : ℝ → ℂ) (hK : Integrable K)
    (hKc : Continuous K) (hHc : Continuous H)
    (hHnorm : ∀ T : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨H, hHc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict T‖))
    (hrepr : ∀ x : ℝ, K x = ∫ y : ℝ, K y * H (x - y))
    (S : TopologicalSpace.Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨K, hKc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
  let T : TopologicalSpace.Compacts ℝ :=
    ⟨(fun p : ℝ × ℝ => p.1 - p.2) '' ((S : Set ℝ) ×ˢ Set.Icc (0 : ℝ) 1),
      (S.isCompact.prod isCompact_Icc).image (continuous_fst.sub continuous_snd)⟩
  let M : ℤ → ℝ := fun n =>
    ‖((⟨H, hHc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict T‖
  have hM : Summable M := hHnorm T
  have hM0 (n : ℤ) : 0 ≤ M n := norm_nonneg _
  let C := ∑' n : ℤ, M n
  have hMC (n : ℤ) : M n ≤ C := hM.le_tsum n (fun j _ => hM0 j)
  let g : ℤ → ℝ → ℝ := fun n y => ‖K y‖ * M (n - ⌊y⌋)
  have hg0 (n : ℤ) (y : ℝ) : 0 ≤ g n y := mul_nonneg (norm_nonneg _) (hM0 _)
  have hgi (n : ℤ) : Integrable (g n) := by
    have hm : Measurable (fun y : ℝ => M (n - ⌊y⌋)) :=
      (measurable_of_countable M).comp (measurable_const.sub Int.measurable_floor)
    apply hK.norm.mul_bdd hm.aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hM0 _)]
    exact hMC _
  have hHbound (n : ℤ) (x : S) (y : ℝ) :
      ‖H ((x : ℝ) + (n : ℝ) - y)‖ ≤ M (n - ⌊y⌋) := by
    let z : T := ⟨(x : ℝ) - Int.fract y,
      ⟨((x : ℝ), Int.fract y),
        ⟨x.property, ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩⟩, rfl⟩⟩
    have he : (x : ℝ) + (n : ℝ) - y =
        (z : ℝ) + ((n - ⌊y⌋ : ℤ) : ℝ) := by
      dsimp only [z]
      simp only [Int.fract, Int.cast_sub]
      ring
    rw [he]
    exact ContinuousMap.norm_coe_le_norm
      (((⟨H, hHc⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight ((n - ⌊y⌋ : ℤ) : ℝ))).restrict T) z
  have hsup (n : ℤ) :
      ‖((⟨K, hKc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖ ≤
        ∫ y : ℝ, g n y := by
    apply (ContinuousMap.norm_le _ (integral_nonneg (hg0 n))).mpr
    intro x
    change ‖K ((x : ℝ) + (n : ℝ))‖ ≤ _
    rw [hrepr ((x : ℝ) + (n : ℝ))]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) (hgi n)
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hHbound n x y) (norm_nonneg _)
  have hsumM (s : Finset ℤ) (y : ℝ) : ∑ n ∈ s, M (n - ⌊y⌋) ≤ C := by
    have hs : Summable (fun n : ℤ => M (n - ⌊y⌋)) :=
      (Equiv.summable_iff (f := M) (Equiv.subRight (⌊y⌋ : ℤ))).mpr hM
    have ht : (∑' n : ℤ, M (n - ⌊y⌋)) = C := (Equiv.subRight ⌊y⌋).tsum_eq M
    exact (hs.sum_le_tsum s (fun n _ => hM0 _)).trans_eq ht
  apply summable_of_sum_le (fun n => norm_nonneg _) (c := (∫ y : ℝ, ‖K y‖) * C)
  intro s
  calc
    _ ≤ ∑ n ∈ s, ∫ y : ℝ, g n y := Finset.sum_le_sum (fun n _ => hsup n)
    _ = ∫ y : ℝ, ∑ n ∈ s, g n y :=
      (integral_finsetSum s (fun n _ => hgi n)).symm
    _ ≤ ∫ y : ℝ, ‖K y‖ * C := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun y => Finset.sum_nonneg (fun n _ => hg0 n y)))
        (hK.norm.mul_const C)
      filter_upwards with y
      change (∑ n ∈ s, ‖K y‖ * M (n - ⌊y⌋)) ≤ ‖K y‖ * C
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hsumM s y) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

end LeanLab.ExceptionalSet.Decomp464h

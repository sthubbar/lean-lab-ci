import LeanLab.ExceptionalSet.Decomp450a

/-!
P0082 page 356, the unnumbered Poisson display in the proof of Lemma 1.
Source: https://doi.org/10.5802/aif.1621
These implications expose the existing local normal convergence input.
They do not assert that input for every bandlimited integrable kernel.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462a

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR)

/-- P0082 page 356, auxiliary continuity justification for the Poisson display.
CONDITIONAL ON local normal convergence of the unmodulated translates.
Modulation preserves all compact translate norms. -/
theorem continuous_of_translate_norm (K : ℝ → ℂ) (hcont : Continuous K)
    (hnorm : ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖))
    (v : ℝ) :
    Continuous (fun x : ℝ => ∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) := by
  let f : C(ℝ, ℂ) := ⟨fun x => K x * eC (-(x * v)),
    hcont.mul (by unfold eC; fun_prop)⟩
  have hf : ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
    intro S
    convert hnorm S using 1
    funext n
    exact Decomp450a.modulated_translate_norm K hcont v S n
  have hs := ContinuousMap.summable_of_locally_summable_norm hf
  convert (map_continuous (∑' n : ℤ, f.comp (ContinuousMap.addRight (n : ℝ)))) using 1
  funext x
  exact ContinuousMap.tsum_apply hs x

/-- P0082 page 356, the transform computation in the proof of Lemma 1.
CONDITIONAL ON local normal convergence of the unmodulated translates.
Folding the periodization gives its coefficient as the shifted transform. -/
theorem fourier_coeff_of_translate_norm (K : ℝ → ℂ) (hcont : Continuous K)
    (hnorm : ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖))
    (v : ℝ) (m : ℤ) :
    (∫ x in (0 : ℝ)..1,
        (∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) * eC (-(x * (m : ℝ)))) =
      ftR K (v + (m : ℝ)) := by
  let f : C(ℝ, ℂ) := ⟨fun x => K x * eC (-(x * v)),
    hcont.mul (by unfold eC; fun_prop)⟩
  have hf : ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
    intro S
    convert hnorm S using 1
    funext n
    exact Decomp450a.modulated_translate_norm K hcont v S n
  have hs := ContinuousMap.summable_of_locally_summable_norm hf
  rw [← Decomp450a.fourier_modulated K v (m : ℝ)]
  change _ = FourierTransform.fourier (f : ℝ → ℂ) (m : ℝ)
  rw [← Real.fourierCoeff_tsum_comp_add hf m,
    fourierCoeff_eq_intervalIntegral _ m 0]
  simp only [div_one, one_smul, zero_add]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  simp only [Function.Periodic.lift_coe, zsmul_one, smul_eq_mul]
  rw [← ContinuousMap.tsum_apply hs]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, ContinuousMap.coe_mk]
  rw [mul_comm]
  congr 1
  rw [fourier_coe_apply]
  unfold eC
  simp only [Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring

end LeanLab.ExceptionalSet.Decomp462a

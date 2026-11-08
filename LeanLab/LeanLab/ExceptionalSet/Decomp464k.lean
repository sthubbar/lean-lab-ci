import LeanLab.ExceptionalSet.Decomp464j
import LeanLab.ExceptionalSet.SPLIT_leaf_poisson_summation
import LeanLab.ExceptionalSet.SPLIT_leaf_product_integrable

/-!
P0082 page 356, the remaining elementary Fourier split supplies.
Absolute local convergence is supplied by the proved bandlimited sampling estimate.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464k

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR)

/-- P0082 page 356, exact generic Fourier input from proved local convergence. -/
theorem periodization_continuous_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    Continuous (fun x : ℝ => ∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) := by
  have he : (fun x : ℝ => ∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) =
      fun x : ℝ => eC (-(x * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(x * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) :=
    funext (Decomp464j.poisson_supplied K hK hcont hsupp v)
  rw [he]
  unfold eC
  fun_prop

/-- P0082 page 356, exact generic Fourier input from proved local convergence. -/
theorem periodization_fourier_coeff_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) (m : ℤ) :
    (∫ x in (0 : ℝ)..1,
        (∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) * eC (-(x * (m : ℝ)))) =
      ftR K (v + (m : ℝ)) := by
  let f : C(ℝ, ℂ) := ⟨fun x => K x * eC (-(x * v)),
    hcont.mul (by unfold eC; fun_prop)⟩
  have hfnorm (S : TopologicalSpace.Compacts ℝ) :
      Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
    convert Decomp464i.leaf_translate_norm_supplied K hK hcont hsupp S using 1
    funext n
    exact Decomp450a.modulated_translate_norm K hcont v S n
  have hf : Summable (fun n : ℤ => f.comp (ContinuousMap.addRight (n : ℝ))) :=
    ContinuousMap.summable_of_locally_summable_norm hfnorm
  have hv (x : ℝ) :
      (Function.Periodic.lift (f.periodic_tsum_comp_add_zsmul (1 : ℝ))) (x : UnitAddCircle) =
        ∑' n : ℤ, K (x + n) * eC (-((x + n) * v)) := by
    simpa only [Function.Periodic.lift_coe, zsmul_one, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight, f, ContinuousMap.coe_mk] using
        (ContinuousMap.hasSum_apply hf.hasSum x).tsum_eq.symm
  have he (x : ℝ) : fourier (-m) (x : UnitAddCircle) = eC (-(x * (m : ℝ))) := by
    rw [fourier_coe_apply]
    unfold eC
    congr 1
    push_cast
    ring
  have hc := Real.fourierCoeff_tsum_comp_add (f := f) hfnorm m
  rw [fourierCoeff_eq_intervalIntegral _ m 0] at hc
  simp only [div_one, one_smul, zero_add, smul_eq_mul] at hc
  have hr : FourierTransform.fourier (f : ℝ → ℂ) m = ftR K (v + (m : ℝ)) :=
    Decomp450a.fourier_modulated K v m
  simpa only [hv, he, mul_comm] using hc.trans hr

/-- P0082 page 356, exact generic Fourier input from proved local convergence. -/
theorem kernel_sup_summable_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≠ ⊤ := by
  let S : TopologicalSpace.Compacts ℝ := ⟨Set.Icc (0 : ℝ) 1, isCompact_Icc⟩
  let M : ℤ → ℝ := fun n =>
    ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖
  have hM : Summable M := Decomp464i.leaf_translate_norm_supplied K hK hcont hsupp S
  have hsup (n : ℤ) :
      (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≤ ENNReal.ofReal (M n) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply ENNReal.ofReal_le_ofReal
    let z : S := ⟨t - (n : ℝ), by
      constructor <;> linarith [ht.1, ht.2]⟩
    have hp := ContinuousMap.norm_coe_le_norm
      (((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S) z
    change ‖K ((z : ℝ) + (n : ℝ))‖ ≤ M n at hp
    have he : (z : ℝ) + (n : ℝ) = t := by dsimp only [z]; ring
    simpa only [he] using hp
  exact ne_of_lt ((ENNReal.tsum_le_tsum hsup).trans_lt hM.tsum_ofReal_lt_top)

end LeanLab.ExceptionalSet.Decomp464k

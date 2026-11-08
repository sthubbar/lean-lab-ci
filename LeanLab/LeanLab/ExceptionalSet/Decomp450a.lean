import LeanLab.ExceptionalSet.SPLIT_leaf_poisson
import LeanLab.ExceptionalSet.Decomp404b

/-!
P0082 page 356, Poisson summation display in the proof of Lemma 1.
Source: https://doi.org/10.5802/aif.1621
The remaining analytic input is local absolute summability of translates of K.
The input has no modulation, transform sum or Poisson identity in its conclusion.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450a

open Real MeasureTheory
open scoped FourierTransform
open LeanLab.ExceptionalSet.U1539 (eC ftR)

/-- LEAF. P0082 page 356, analytic justification of the Poisson display.
For a continuous integrable bandlimited kernel, the sup norms of its integer
translates on every compact set form a summable sequence. This is the local
absolute convergence hypothesis of Mathlib's Poisson theorem. -/
theorem leaf_translate_norm (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0) :
    ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
  sorry

/-- P0082 page 356, the transform computation before the Poisson display.
Modulation of an arbitrary kernel shifts the Fourier variable by v. -/
theorem fourier_modulated (K : ℝ → ℂ) (v y : ℝ) :
    FourierTransform.fourier (fun x : ℝ => K x * eC (-(x * v))) y = ftR K (v + y) := by
  rw [← Decomp404b.ftR_eq_fourier]
  unfold ftR
  apply integral_congr_ae
  filter_upwards with x
  unfold eC
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- P0082 page 356, auxiliary norm identity for the Poisson display.
The modulation has modulus one, so every compact translate sup norm is unchanged. -/
theorem modulated_translate_norm (K : ℝ → ℂ) (hcont : Continuous K)
    (v : ℝ) (S : TopologicalSpace.Compacts ℝ) (n : ℤ) :
    ‖((⟨fun x : ℝ => K x * eC (-(x * v)),
      hcont.mul (by unfold eC; fun_prop)⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight (n : ℝ))).restrict S‖ =
      ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖ := by
  simp only [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.restrict_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.coe_addRight,
    norm_mul, LeanLab.ExceptionalSet.U1539.norm_eC, mul_one]

/-- P0082 page 356, exact summation leaf from its missing local convergence hypothesis.
Fourier summability follows from the two adjacent frequencies already isolated on main. -/
theorem summation_of_translate_norm (K : ℝ → ℂ) (hK : Integrable K)
    (hcont : Continuous K) (hsupp : ∀ ξ : ℝ, 1 < |ξ| → ftR K ξ = 0)
    (hnorm : ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ =>
        ‖((⟨K, hcont⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict S‖))
    (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
  classical
  let f : C(ℝ, ℂ) := ⟨fun x => K x * eC (-(x * v)),
    hcont.mul (by unfold eC; fun_prop)⟩
  have hf (m : ℤ) : FourierTransform.fourier (f : ℝ → ℂ) m = ftR K (v + m) :=
    fourier_modulated K v m
  have hzero (m : ℤ) (hm : m ∉ ({-⌊v⌋, -(⌊v⌋ + 1)} : Finset ℤ)) :
      FourierTransform.fourier (f : ℝ → ℂ) m = 0 := by
    rw [hf]
    apply Decomp371d.leaf_poisson_endpoint K hK hcont hsupp
    apply Decomp371d.leaf_poisson_index v m
    · intro he; exact hm (by simp [he])
    · intro he; exact hm (by simp [he])
  have hfnorm : ∀ S : TopologicalSpace.Compacts ℝ,
      Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
    intro S
    convert hnorm S using 1
    funext n
    exact modulated_translate_norm K hcont v S n
  have hp := Real.tsum_eq_tsum_fourier hfnorm (summable_of_ne_finset_zero hzero) α
  change (∑' n : ℤ, f (α + n)) = _
  rw [hp]
  apply tsum_congr
  intro m
  rw [hf]
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
  have he : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ)) =
      eC (α * (m : ℝ)) := by
    unfold eC
    push_cast
    congr 1
    ring
  rw [he, mul_comm]

/-- P0082 page 356, exact sealed summation statement from the smaller convergence leaf.
This theorem is CONDITIONAL ON leaf_translate_norm and has no admission of its own. -/
theorem summation_assembly (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
  exact summation_of_translate_norm K hK hcont hsupp
    (leaf_translate_norm K hK hcont hsupp) v α

/-- P0082 page 356, exact original two frequency Poisson leaf.
This theorem is CONDITIONAL ON leaf_translate_norm alone. -/
theorem poisson_assembly (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  rw [summation_assembly K hK hcont hsupp v α,
    Decomp371d.leaf_poisson_collapse K hK hcont hsupp v α]

/-- P0082 pages 356 and 357, displays 3 and 4. The nonzero paper kernel
satisfies the translate convergence conclusion without the open generic input. -/
theorem kernel_translate_norm (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (S : TopologicalSpace.Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨fun x : ℝ => (LeanLab.ExceptionalSet.U1539.Kfun Δ x : ℂ),
        KernelTransform264.Kfun_continuous Δ⟩ : C(ℝ, ℂ)).comp
          (ContinuousMap.addRight (n : ℝ))).restrict S‖) := by
  have hd : Asymptotics.IsBigO (Filter.cocompact ℝ)
      (fun x : ℝ => (LeanLab.ExceptionalSet.U1539.Kfun Δ x : ℂ))
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    simpa only [mul_zero, neg_zero, eC, Complex.ofReal_zero,
      Complex.exp_zero, mul_one] using Decomp404b.modulated_kernel_isBigO Δ 0 hΔ hΔ1
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((isBigO_norm_restrict_cocompact
      ⟨_, KernelTransform264.Kfun_continuous Δ⟩ (by norm_num : (0 : ℝ) < 2) hd S).comp_tendsto
        Int.tendsto_coe_cofinite)

end LeanLab.ExceptionalSet.Decomp450a

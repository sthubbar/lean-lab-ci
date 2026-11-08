import LeanLab.ExceptionalSet.Decomp464i
import LeanLab.ExceptionalSet.SPLIT_leaf_poisson_collapse

/-!
P0082 page 356, clean exact supplies for generic Lemma 1 and its Fourier inputs.
Local translate summability is proved, not assumed or admitted.
The Poisson collapse uses the four leaves completed in the assigned unit.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464j

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- P0082 page 356, exact generic Lemma 1 input from the proved convergence estimate.
No admitted analytic input is used. -/
theorem product_integrable_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    Integrable (fun α : ℝ => h α * K α) := by
  exact Decomp450b.product_integrable_of_translate_norm h K hper hh hcont
    (Decomp464i.leaf_translate_norm_supplied K hK hcont hsupp
      ⟨Set.Icc 0 1, isCompact_Icc⟩)

/-- P0082 page 356, exact generic Lemma 1 input from the proved convergence estimate.
No admitted analytic input is used. -/
theorem fold_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ∫ α in (0 : ℝ)..1,
        h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  apply Decomp404b.fold_of_integrable h K hper v
  have he : Continuous (fun α : ℝ => eC (-(α * v))) := by unfold eC; fun_prop
  exact (product_integrable_supplied h K hper hh hK hcont hsupp).mul_bdd
    he.aestronglyMeasurable (Filter.Eventually.of_forall (fun α => (U1539.norm_eC _).le))

/-- P0082 page 356, exact generic Lemma 1 input from the proved convergence estimate.
No admitted analytic input is used. -/
theorem poisson_summation_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
  exact Decomp450a.summation_of_translate_norm K hK hcont hsupp
    (Decomp464i.leaf_translate_norm_supplied K hK hcont hsupp) v α

/-- P0082 page 356, exact generic Lemma 1 input from the proved convergence estimate.
No admitted analytic input is used. -/
theorem poisson_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  rw [poisson_summation_supplied K hK hcont hsupp v α,
    Decomp371d.leaf_poisson_collapse_split K hK hcont hsupp v α]

/-- P0082 page 356 Lemma 1, exact original paper statement.
The fold and Poisson inputs are supplied by clean proofs in this file. -/
theorem lemma1_supplied : LeanLab.ExceptionalSet.U1539.Lemma1 := by
  intro h K hper hh hK hcont hsupp v
  have hg0 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * (⌊v⌋ : ℝ)))) volume 0 1 := by
    apply hh.mul_continuousOn
    unfold eC
    fun_prop
  have hg1 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) volume 0 1 := by
    apply hh.mul_continuousOn
    unfold eC
    fun_prop
  calc
    _ = ∫ α in (0 : ℝ)..1,
        (h α * eC (-(α * (⌊v⌋ : ℝ)))) * ftR K (Int.fract v) +
          (h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) * ftR K (Int.fract v - 1) := by
      rw [fold_supplied h K hper hh hK hcont hsupp v]
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only
      rw [poisson_supplied K hK hcont hsupp v α]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (hg0.mul_const (ftR K (Int.fract v)))
        (hg1.mul_const (ftR K (Int.fract v - 1))),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      unfold hcheck
      ring

end LeanLab.ExceptionalSet.Decomp464j

import LeanLab.ExceptionalSet.Decomp462e
import LeanLab.ExceptionalSet.Decomp450b

/-!
P0082 page 356, the complete generic Lemma 1 and its two proof displays.
Source: https://doi.org/10.5802/aif.1621
The proved translate norm estimate discharges every generic sampling input.
The original sealed declarations outside the assigned unit are left for review.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462f

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck norm_eC)

/-- P0082 page 356, auxiliary integrability for the first proof display.
This supplies the exact generic leaf_product_integrable statement. -/
theorem product_integrable_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    Integrable (fun α : ℝ => h α * K α) := by
  exact Decomp450b.product_integrable_of_translate_norm h K hper hh hcont
    (Decomp462e.translate_norm_supplied K hK hcont hsupp ⟨Set.Icc 0 1, isCompact_Icc⟩)

/-- P0082 page 356, finite norm integral needed in the first proof display.
This supplies the exact leaf_product_norm_hasFiniteIntegral statement. -/
theorem product_norm_hasFiniteIntegral_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    HasFiniteIntegral (fun α : ℝ => ‖h α * K α‖) := by
  exact (product_integrable_supplied h K hper hh hK hcont hsupp).norm.2

/-- P0082 page 356, integrability of the modulated product in Lemma 1. -/
theorem modulated_product_integrable_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    Integrable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
  have he : Continuous (fun α : ℝ => eC (-(α * v))) := by unfold eC; fun_prop
  exact (product_integrable_supplied h K hper hh hK hcont hsupp).mul_bdd
    he.aestronglyMeasurable (Filter.Eventually.of_forall fun α => (norm_eC _).le)

/-- P0082 page 356, the first proof display of Lemma 1.
This supplies the exact generic Decomp371d.leaf_fold statement. -/
theorem fold_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ∫ α in (0 : ℝ)..1,
        h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  exact Decomp404b.fold_of_integrable h K hper v
    (modulated_product_integrable_supplied h K hper hh hK hcont hsupp v)

/-- P0082 page 356, the full Poisson summation display before support collapse.
This supplies the exact leaf_poisson_summation statement. -/
theorem poisson_summation_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      ∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) := by
  exact Decomp450a.summation_of_translate_norm K hK hcont hsupp
    (Decomp462e.translate_norm_supplied K hK hcont hsupp) v α

/-- P0082 page 356, the two adjacent frequencies in the Poisson display.
This supplies the exact generic Decomp371d.leaf_poisson statement. -/
theorem poisson_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  rw [poisson_summation_supplied K hK hcont hsupp v α,
    Decomp371d.leaf_poisson_collapse K hK hcont hsupp v α]

/-- P0082 page 356, the full printed Lemma 1 with no cited input.
The statement is the exact existing U1539.Lemma1 proposition. -/
theorem lemma1_supplied : LeanLab.ExceptionalSet.U1539.Lemma1 := by
  intro h K hper hh hK hcont hsupp v
  exact Decomp450b.lemma1_of_translate_norm h K hper hh hK hcont hsupp
    (Decomp462e.translate_norm_supplied K hK hcont hsupp) v

end LeanLab.ExceptionalSet.Decomp462f

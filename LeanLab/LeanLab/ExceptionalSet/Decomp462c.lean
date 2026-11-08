import LeanLab.ExceptionalSet.Decomp462b

/-!
P0082 page 356, auxiliary analytic justification of the first proof display.
Source: https://doi.org/10.5802/aif.1621
These bounds isolate the interval supremum and nonnegative integral steps.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462c

open Real MeasureTheory
open scoped ENNReal
open LeanLab.ExceptionalSet.U1539 (ftR)
/-- P0082 page 356, nonnegative sum and integral exchange used in the fold.
No measurability assumption is needed for this inequality. -/
theorem tsum_lintegral_le (f : ℤ → ℝ → ℝ≥0∞) :
    (∑' n : ℤ, ∫⁻ y : ℝ, f n y) ≤ ∫⁻ y : ℝ, ∑' n : ℤ, f n y := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc
    _ ≤ ∫⁻ y : ℝ, ∑ n ∈ s, f n y := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert n s hn ih =>
        simp only [Finset.sum_insert hn]
        exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
    _ ≤ _ := lintegral_mono fun y => ENNReal.sum_le_tsum s
/-- P0082 page 356, auxiliary interval supremum bound for sampling.
This is the exact leaf_split_interval_sup_le statement with a new name. -/
theorem split_interval_sup_le_supplied (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (φ : ℝ → ℂ) (hφ : Integrable φ)
    (hφhat : ∀ α : ℝ, |α| ≤ 1 → ftR φ α = 1) (n : ℤ) :
    (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≤
      ∫⁻ y : ℝ,
        (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
          ENNReal.ofReal ‖K y‖ := by
  refine iSup₂_le fun t ht => ?_
  rw [← Decomp462b.split_conv_eq_supplied K hK hcont hsupp φ hφ hφhat t]
  calc
    _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal ‖φ (t - y) * K y‖ := by
      simpa only [ofReal_norm] using
        enorm_integral_le_lintegral_enorm (fun y : ℝ => φ (t - y) * K y)
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      gcongr
      exact le_iSup₂_of_le t ht le_rfl

/-- P0082 page 356, auxiliary exchange of interval weights and integration.
This is the exact leaf_split_tsum_integral_le statement with a new name. -/
theorem split_tsum_integral_le_supplied (K : ℝ → ℂ) (φ : ℝ → ℂ) :
    (∑' n : ℤ, ∫⁻ y : ℝ,
        (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
          ENNReal.ofReal ‖K y‖) ≤
      ∫⁻ y : ℝ,
        (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
          ENNReal.ofReal ‖K y‖ := by
  simpa only [ENNReal.tsum_mul_right] using
    tsum_lintegral_le (fun n y =>
      (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
        ENNReal.ofReal ‖K y‖)

end LeanLab.ExceptionalSet.Decomp462c

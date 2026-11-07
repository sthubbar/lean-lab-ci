import LeanLab.ExceptionalSet.Decomp446b

/-!
Split of the product integrability step of the generic Fourier fold.

A merely periodic `L¹` factor times a kernel of compact Fourier support is
integrable. The proof cuts the real line into unit half open intervals, keeps one
period of the periodic factor on each of them, and is left with the sup norms of
the kernel on the unit intervals, which are summable because an integrable kernel
with compact Fourier support has summable interval sup norms.

The four lemmas marked LEAF below are the open work items; the assembly at the
end of the file derives the target statement from them.
-/

namespace LeanLab.ExceptionalSet.Decomp446b

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck norm_eC)

/-- LEAF. Step 1 of the proof: measurability of the pointwise product. A function
that is periodic of period one and interval integrable over one period is almost
everywhere strongly measurable, a continuous function is strongly measurable, and
a pointwise product of two almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
theorem leaf_product_aestronglyMeasurable (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hcont : Continuous K) :
    AEStronglyMeasurable (fun α : ℝ => h α * K α) := by
  sorry

/-- LEAF. Step 2 of the proof: the unit interval partition of the absolute
integral. The half open unit intervals with integer endpoints are pairwise
disjoint and cover the real line, so the integral of the absolute value of the
product equals the sum over the integers of its integrals over those intervals.
No measurability of the integrand is needed for this step. -/
theorem leaf_lintegral_unit_partition (h K : ℝ → ℂ) :
    ∫⁻ α : ℝ, ENNReal.ofReal ‖h α * K α‖ =
      ∑' n : ℤ, ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α * K α‖ := by
  sorry

/-- LEAF. Step 3 of the proof: the bound on a single unit interval. On the
interval from `n` to `n + 1` the periodic factor takes only its values from one
period, and the continuous kernel is dominated there by the supremum of its norm
on that same interval, so the integral over the interval is at most one period of
the periodic factor times that supremum. -/
theorem leaf_unit_interval_bound (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hcont : Continuous K) (n : ℤ) :
    ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α * K α‖ ≤
      (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) *
        (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) := by
  sorry

/-- LEAF. Step 4 of the proof: the weights are summable. For an integrable
continuous kernel whose Fourier transform vanishes outside the interval from `-1`
to `1`, the supremum of its norm over the unit interval starting at `n` is a
summable function of the integer `n`. This is the analytic input of the split: it
is a statement about the kernel alone and does not mention the periodic factor. -/
theorem leaf_kernel_sup_summable (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≠ ⊤ := by
  sorry

/-- Assembly. Product integrability from the four steps above: measure the
product, split the absolute integral over the unit intervals, bound each piece by
one period of the periodic factor times the kernel supremum on that interval, and
sum the resulting weights. -/
theorem leaf_product_integrable_split (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    Integrable (fun α : ℝ => h α * K α) := by
  refine ⟨leaf_product_aestronglyMeasurable h K hper hh hcont, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hC : (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) ≠ ⊤ := by
    have h := hh.1.2
    rw [hasFiniteIntegral_iff_norm] at h
    simpa only [IntegrableOn] using h.ne
  have hsup : (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≠ ⊤ :=
    leaf_kernel_sup_summable K hK hcont hsupp
  calc
    ∫⁻ α, ENNReal.ofReal ‖h α * K α‖
        = ∑' n : ℤ,
            ∫⁻ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖h α * K α‖ :=
          leaf_lintegral_unit_partition h K
    _ ≤ ∑' n : ℤ, (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) *
            (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) :=
          ENNReal.tsum_le_tsum fun n => leaf_unit_interval_bound h K hper hh hcont n
    _ = (∫⁻ α in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖h α‖) *
          ∑' n : ℤ, (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) :=
          ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) (lt_top_iff_ne_top.mpr hsup)

end LeanLab.ExceptionalSet.Decomp446b

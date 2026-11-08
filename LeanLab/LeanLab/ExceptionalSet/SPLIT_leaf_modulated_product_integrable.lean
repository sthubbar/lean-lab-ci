/-
Split of `leaf_modulated_product_integrable`, the first step of the Poisson fold of this
folder, into its two ingredients: the phase `α ↦ e(-αv)` has norm one, so it drops out of
a pointwise norm bound, and the unmodulated product `α ↦ h α * K α` of a merely periodic
`L¹` factor with a continuous integrable kernel of compact Fourier support is integrable,
by folding the line into unit periods and summing the kernel over the translates.

`leaf_modulated_product_integrable_split` below states the split target unchanged and is
assembled from the four leaves, so it carries no `sorry` of its own. The leaves are open
work items.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma1

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. Step 1 of the proof, the phase is unimodular: for every real `α` the norm of
`h α * K α * e(-αv)` equals the norm of `h α * K α`, because `e(x)` has norm one for every
real `x`. The step is a pointwise identity: it mentions neither integrability nor the
Fourier support of the kernel, and it carries no hypothesis at all. At `v = 0` both sides
are the same expression, at `α = 0` both sides are `‖h 0 * K 0‖`, and for negative `v` the
identity is unchanged since only `‖e(-αv)‖ = 1` is used. -/
theorem leaf_modulation_norm (h K : ℝ → ℂ) (v : ℝ) :
    ∀ α : ℝ, ‖h α * K α * eC (-(α * v))‖ = ‖h α * K α‖ := by
  sorry

/-- LEAF. Step 2 of the proof, the modulated product is almost everywhere strongly
measurable: a function of period one that is interval integrable over one period is almost
everywhere strongly measurable on the whole line, a continuous kernel is strongly
measurable, and the two factors of the product together with the continuous phase
`α ↦ e(-αv)` give an almost everywhere strongly measurable product. This is the
measurability half of the integrability criterion and says nothing about any integral. -/
theorem leaf_modulated_aestronglyMeasurable (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hcont : Continuous K) (v : ℝ) :
    AEStronglyMeasurable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
  sorry

/-- LEAF. Step 3 of the proof, the unmodulated product is measurable in norm: the same
periodic and continuous factors as in step 2, without the phase, give an almost everywhere
strongly measurable real valued function `α ↦ ‖h α * K α‖`. It is the measurability half of
the step that follows and holds with no hypothesis on the Fourier transform of the
kernel. -/
theorem leaf_product_norm_aestronglyMeasurable (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hcont : Continuous K) :
    AEStronglyMeasurable (fun α : ℝ => ‖h α * K α‖) := by
  sorry

/-- LEAF. Step 4 of the proof, the envelope of the unmodulated product has finite total
mass: for `h` of period one and integrable on one period, and for `K` integrable,
continuous, with Fourier transform vanishing outside the interval from `-1` to `1`, the
absolute integral `∫⁻ α, ‖h α * K α‖` is finite. This is the analytic step of the split and
the only one that uses the compact Fourier support: it cuts the line into the unit
intervals `(n, n+1]`, replaces `h` there by its one period and `K` by its supremum on that
interval, and needs the translate sums of those suprema to be summable. It states the
finiteness alone, not the integrability it serves, and it is the case `v = 0` of the phase
in the target. -/
theorem leaf_product_norm_hasFiniteIntegral (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    HasFiniteIntegral (fun α : ℝ => ‖h α * K α‖) := by
  sorry

/-! ### Assembly -/

/-- The split target unchanged: the modulated product is integrable. The unmodulated
envelope is integrable by steps 3 and 4, the modulated product is measurable by step 2 and
is dominated pointwise in norm by that envelope by step 1, so the integrability criterion
for a dominated measurable function applies. -/
theorem leaf_modulated_product_integrable_split (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K) (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) : Integrable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
  have hg : Integrable (fun α : ℝ => ‖h α * K α‖) :=
    ⟨leaf_product_norm_aestronglyMeasurable h K hper hh hcont,
      leaf_product_norm_hasFiniteIntegral h K hper hh hK hcont hsupp⟩
  refine Integrable.mono' hg (leaf_modulated_aestronglyMeasurable h K hper hh hcont v) ?_
  filter_upwards with α
  exact le_of_eq (leaf_modulation_norm h K v α)

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.leaf_modulated_product_integrable_split

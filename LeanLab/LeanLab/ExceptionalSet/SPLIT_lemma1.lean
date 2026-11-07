/-
Split of `lemma1`, the Poisson summation identity of this folder, into the three steps
of its written proof: the integrability of the modulated product, the fold of the real
line into the unit interval by the period of `h`, and the reduction of the folded
kernel sum to its two adjacent Fourier frequencies.

`lemma1_split` below states `Lemma1` unchanged and is assembled from the three leaves,
so it carries no `sorry` of its own. Each leaf carries exactly one step.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. Step 1 of the proof, the integrability of the integrand: for periodic `h`
that is interval integrable on `[0,1]` and for `K` integrable, continuous and with
Fourier transform vanishing outside `[-1,1]`, the modulated product
`α ↦ h α * K α * e(-αv)` is integrable on the whole line.

This is the step that uses the compact Fourier support of `K`: it bounds `K` by the
`L¹` norm of its transform and then controls the unbounded periodic factor `h` one
unit interval at a time. It is stated with no periodization, no `tsum` and no Fourier
coefficient on the right, so it is strictly weaker than the split's main statement. -/
theorem leaf_modulated_product_integrable (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    Integrable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
  sorry

/-- LEAF. Step 2 of the proof, the fold: with the modulated product integrable, the
integral of `h α * K α * e(-αv)` over the whole real line equals the integral over one
period `[0,1]` of `h α` against the sum of the integer translates of `K` modulated at
`v`. The period of `h` is what moves it out of the sum. -/
theorem leaf_fold (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v : ℝ)
    (hg : Integrable (fun α : ℝ => h α * K α * eC (-(α * v)))) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ∫ α in (0 : ℝ)..1, h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  sorry

/-- LEAF. Step 3 of the proof, the Poisson evaluation of the folded kernel: for every
shift `α` the sum of the integer translates of `K` modulated at `v` reduces to the two
adjacent Fourier frequencies of `v`, with the coefficients `ftR K (Int.fract v)` and
`ftR K (Int.fract v - 1)`. Only the translate sums survive, so no `h` appears here. -/
theorem leaf_poisson (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  sorry

/-! ### Assembly -/

/-- Lemma 1 from the three leaves above: the unchanged statement of `lemma1`. -/
theorem lemma1_split : Lemma1 := by
  intro h K hper hh hK hcont hsupp v
  have hg := leaf_modulated_product_integrable h K hper hh hK hcont hsupp v
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
      rw [leaf_fold h K hper v hg]
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only
      rw [leaf_poisson K hK hcont hsupp v α]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (hg0.mul_const (ftR K (Int.fract v)))
        (hg1.mul_const (ftR K (Int.fract v - 1))),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      unfold hcheck
      ring

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma1_split

import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.KernelTransform264

/-!
Task371 splits P0082 Lemma 1 at the two steps in its written proof on page 356.
Source: https://doi.org/10.5802/aif.1621 pages 355 and 356.
The bandlimited sampling and periodization estimates remain open analytic inputs.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371d

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- LEAF. P0082 page 356, first display of the proof of Lemma 1. Fold the real
line into unit intervals and use the period of h. Compact Fourier support of K
is retained to control the periodized absolute values against a merely L1 function h. -/
theorem leaf_fold (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ∫ α in (0 : ℝ)..1,
        h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  sorry

/-- LEAF. P0082 page 356, Poisson summation display in the proof of Lemma 1.
For the shifted modulated kernel, only the two adjacent Fourier frequencies remain.
The compact support and continuity make the endpoint Fourier values vanish. -/
theorem leaf_poisson (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  sorry

/-- Assembly. The exact existing Lemma1 type from the two written proof steps.
Conditional on the periodization and Poisson leaves above. -/
theorem lemma1_assembly : LeanLab.ExceptionalSet.U1539.Lemma1 := by
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
      rw [leaf_fold h K hper hh hK hcont hsupp v]
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

/-- Nonzero paper kernel at Delta equal to one eighth. It satisfies the three
kernel hypotheses in Lemma 1, so neither open leaf has an empty kernel domain. -/
theorem kernel_instance :
    Integrable (fun x : ℝ => (LeanLab.ExceptionalSet.U1539.Kfun (1 / 8) x : ℂ)) ∧
    Continuous (fun x : ℝ => (LeanLab.ExceptionalSet.U1539.Kfun (1 / 8) x : ℂ)) ∧
    (∀ α : ℝ, 1 < |α| → ftR (fun x : ℝ => (LeanLab.ExceptionalSet.U1539.Kfun (1 / 8) x : ℂ)) α = 0) ∧
    LeanLab.ExceptionalSet.U1539.Kfun (1 / 8) 0 ≠ 0 := by
  refine ⟨KernelTransform264.Kfun_integrable (by norm_num) (by norm_num),
    KernelTransform264.Kfun_continuous _, ?_, ?_⟩
  · intro α hα
    exact KernelTransform264.ftR_Kfun_zero (by norm_num) (by norm_num) hα.le
  · norm_num [LeanLab.ExceptionalSet.U1539.Kfun]

end LeanLab.ExceptionalSet.Decomp371d

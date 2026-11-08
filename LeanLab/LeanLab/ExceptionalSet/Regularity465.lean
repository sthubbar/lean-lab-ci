import LeanLab.ExceptionalSet.Decomp404b

/-!
Elementary regularity companions for the remaining Poisson and fold splits.
Source: P0082 page356, Lemma1 and its first proof display.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real MeasureTheory Filter Topology
open LeanLab.ExceptionalSet.U1539 (eC ftR norm_eC)

/-- P0082 page356 first proof display. Periodic local L1 functions are
almost everywhere strongly measurable on the real line. -/
theorem periodic_aestronglyMeasurable (h : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) : AEStronglyMeasurable h := by
  have hperiod (n : ℤ) (x : ℝ) : h (x + n) = h x := by
    simpa only [mul_one] using hper.int_mul n x
  have hhn (n : ℤ) : IntervalIntegrable h volume (n : ℝ) (n + 1) := by
    have hi := hh.comp_add_right (-(n : ℝ))
    simp only [show (fun x : ℝ => h (x + -(n : ℝ))) = h from
      funext (fun x => by simpa only [Int.cast_neg] using hperiod (-n) x)] at hi
    convert hi using 1 <;> ring
  have hm (n : ℤ) : AEStronglyMeasurable h (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp (hhn n)).aestronglyMeasurable
  simpa only [iUnion_Ioc_intCast, Measure.restrict_univ] using AEStronglyMeasurable.iUnion hm

/-- P0082 page356 first proof display. The phase factor preserves norms.
This is the exact leaf_modulation_norm statement. -/
theorem modulation_norm_supplied (h K : ℝ → ℂ) (v : ℝ) :
    ∀ α : ℝ, ‖h α * K α * eC (-(α * v))‖ = ‖h α * K α‖ := by
  intro α
  rw [norm_mul, norm_eC, mul_one]

/-- P0082 page356 first proof display. Exact measurability leaf for the
modulated product. No compact Fourier support estimate is needed. -/
theorem modulated_measurable_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hcont : Continuous K) (v : ℝ) :
    AEStronglyMeasurable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
  have he : Continuous (fun α : ℝ => eC (-(α * v))) := by unfold eC; fun_prop
  exact ((periodic_aestronglyMeasurable h hper hh).mul hcont.aestronglyMeasurable).mul
    he.aestronglyMeasurable

/-- P0082 page356 first proof display. Exact norm measurability leaf for
the unmodulated product. It does not assert finite total mass. -/
theorem product_norm_measurable_supplied (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hcont : Continuous K) :
    AEStronglyMeasurable (fun α : ℝ => ‖h α * K α‖) :=
  ((periodic_aestronglyMeasurable h hper hh).mul hcont.aestronglyMeasurable).norm

/-- P0082 page356 Lemma1. Exact Fourier continuity leaf, using Mathlib's
Fourier integral continuity theorem and the existing normalization identity. -/
theorem ftR_continuous_supplied (K : ℝ → ℂ) (hK : Integrable K) : Continuous (ftR K) := by
  have he : ftR K = FourierTransform.fourier K := funext (Decomp404b.ftR_eq_fourier K)
  rw [he]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hK

/-- P0082 page356 Lemma1, endpoint support by continuity.
This is the exact rescaling limit leaf. -/
theorem rescale_tendsto_supplied (ξ : ℝ) :
    Tendsto (fun n : ℕ => ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))) atTop (nhds ξ) := by
  have hplus : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1))
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hplus
  simpa only [one_div, add_zero, mul_one] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hi).const_mul ξ

/-- P0082 page356 Lemma1, endpoint support by continuity.
This is the exact strict support step for every rescaled frequency. -/
theorem rescale_abs_gt_one_supplied (ξ : ℝ) (hξ : 1 ≤ |ξ|) (n : ℕ) :
    1 < |ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))| := by
  have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  rw [abs_mul, abs_of_pos (show 0 < 1 + (1 : ℝ) / ((n : ℝ) + 1) by positivity)]
  nlinarith

/-- P0082 page356 Lemma1, endpoint support by continuity.
This is the exact limit vanishing leaf. -/
theorem eq_zero_of_tendsto_supplied {f : ℝ → ℂ} {u : ℕ → ℝ} {ξ : ℝ}
    (hf : Continuous f) (hu : Tendsto u atTop (nhds ξ)) (h0 : ∀ n : ℕ, f (u n) = 0) :
    f ξ = 0 := by
  have ht := hf.continuousAt.tendsto.comp hu
  have heq : (fun n => f (u n)) = fun _ => (0 : ℂ) := funext h0
  change Tendsto (fun n => f (u n)) atTop (nhds (f ξ)) at ht
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end LeanLab.ExceptionalSet.Supply465

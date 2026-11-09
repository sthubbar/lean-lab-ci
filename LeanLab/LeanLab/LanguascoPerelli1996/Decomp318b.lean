import LeanLab.LanguascoPerelli1996.Decomp318a
import LeanLab.LanguascoPerelli1996.Point381

/-!
P0071 page 355 display 13, full variation from the proved derivative mass.
This file has no cited analytic input.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp318b
open Real MeasureTheory intervalIntegral
open scoped ContDiff

/-- Page 355, Cauchy Schwarz before display 13, for every smooth complex function. -/
theorem variation_cauchy {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    (∫ v in (-1 : ℝ)..1, |deriv (fun t => ‖f t‖ ^ 2) v|) ≤
      2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖f v‖ ^ 2) *
        Real.sqrt (∫ v in (-1 : ℝ)..1, ‖deriv f v‖ ^ 2) := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hgc := hf.norm_sq ℂ
  have hgg : Continuous (deriv (fun t => ‖f t‖ ^ 2)) := hgc.continuous_deriv (by simp)
  have hd (t : ℝ) : |deriv (fun t => ‖f t‖ ^ 2) t| ≤ 2 * (‖f t‖ * ‖deriv f t‖) := by
    rw [(hf.differentiable (by simp) t).hasDerivAt.norm_sq.deriv, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) _ _) (by norm_num)
  have hm := integral_mono_on (μ := volume) (show (-1 : ℝ) ≤ 1 by norm_num)
    (hgg.abs.intervalIntegrable _ _)
    ((continuous_const.mul (hf.continuous.norm.mul hdc.norm)).intervalIntegrable _ _)
    (fun t _ => hd t)
  have hcs := Point381.integral_mul_le_sqrt (show (-1 : ℝ) ≤ 1 by norm_num)
    hf.continuous.norm hdc.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  simp only [Pi.mul_apply] at hm
  rw [intervalIntegral.integral_const_mul] at hm
  nlinarith

/-- Page 355 display 13. The complete variation estimate for the actual zero band.
The hypotheses and energy agree with the sealed Decomp108 variation_control. -/
theorem band_variation_control :
    GRH → ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          (∫ v in (-1 : ℝ)..1,
            |deriv (fun t => ‖zSum (X * Real.exp t) U T q a‖ ^ 2) v|) ≤ B * T * M := by
  intro hGRH
  obtain ⟨C, hC, hd⟩ := Decomp318a.band_derivative_mass_decomposed hGRH
  refine ⟨4 * Real.exp 2 + C, by positivity, ?_⟩
  intro X hX U T hU hUT hT q inst a ha M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM U le_rfl hUT.le)
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hm : (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) ≤
      (4 * Real.exp 2) * M := by
    have hb := Mass108.band_local_mass hX U T hUT.le q a
    have he := Real.exp_pos (2 : ℝ)
    have hu := hM U le_rfl hUT.le
    have ht := hM T hUT.le le_rfl
    nlinarith
  have hd' := hd X hX U T hU hUT hT q a ha M hM
  have hs : Real.sqrt (C * T ^ 2 * M) = T * Real.sqrt (C * M) := by
    rw [show C * T ^ 2 * M = T ^ 2 * (C * M) by ring,
      Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0]
  have hy : 2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * M) ≤
      (4 * Real.exp 2) * M + C * M := by
    nlinarith [sq_nonneg (Real.sqrt ((4 * Real.exp 2) * M) - Real.sqrt (C * M)),
      Real.sq_sqrt (show 0 ≤ (4 * Real.exp 2) * M by positivity),
      Real.sq_sqrt (mul_nonneg hC hM0)]
  calc
    _ ≤ 2 * Real.sqrt (∫ v in (-1 : ℝ)..1, ‖zSum (X * Real.exp v) U T q a‖ ^ 2) *
        Real.sqrt (∫ v in (-1 : ℝ)..1,
          ‖deriv (fun t : ℝ => zSum (X * Real.exp t) U T q a) v‖ ^ 2) :=
      variation_cauchy (Band108.band_contDiff hX U T q a)
    _ ≤ 2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * T ^ 2 * M) := by
      gcongr
    _ = T * (2 * Real.sqrt ((4 * Real.exp 2) * M) * Real.sqrt (C * M)) := by
      rw [hs]; ring
    _ ≤ T * ((4 * Real.exp 2) * M + C * M) := mul_le_mul_of_nonneg_left hy hT0
    _ = (4 * Real.exp 2 + C) * T * M := by ring

end LeanLab.LanguascoPerelli1996.Decomp318b

#print axioms LeanLab.LanguascoPerelli1996.Decomp318b.variation_cauchy
#print axioms LeanLab.LanguascoPerelli1996.Decomp318b.band_variation_control

/-
P0076 Section 11, page 47. The continuity step for the epsilon perturbed sieve parameters.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.SieveStability

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

namespace LeanLab.Teravainen2016

noncomputable def sieveRhoOne (ε : ℝ) : ℝ := sieveClip (2 / 5) (49 / 100) (19 / 40 - ε)
noncomputable def sieveRhoTwo (ε : ℝ) : ℝ := sieveClip (2 / 5) (49 / 100) (57 / 140 - ε)
noncomputable def sieveSigma (ε : ℝ) : ℝ := sieveClip 3 (7 / 2) (120 / 37 + ε)

noncomputable def stableSieveGap (ε : ℝ) : ℝ :=
  sieveLeftClosed (sieveRhoTwo ε) (sieveSigma ε) -
    (sieveRhoOne ε)⁻¹ * stableSieveRightIntegral (sieveSigma ε) - 1 / (10 : ℝ) ^ 10

/-- The clipped gap is continuous on the whole parameter line. -/
theorem continuous_stableSieveGap : Continuous stableSieveGap := by
  have h1 : Continuous sieveRhoOne := by unfold sieveRhoOne sieveClip; fun_prop
  have h2 : Continuous sieveRhoTwo := by unfold sieveRhoTwo sieveClip; fun_prop
  have hs : Continuous sieveSigma := by unfold sieveSigma sieveClip; fun_prop
  have h1b : ∀ ε, (2 : ℝ) / 5 ≤ sieveRhoOne ε := fun ε =>
    (sieveClip_bounds (by norm_num : (2 : ℝ) / 5 ≤ 49 / 100) _).1
  have h2b : ∀ ε, (2 : ℝ) / 5 ≤ sieveRhoTwo ε := fun ε =>
    (sieveClip_bounds (by norm_num : (2 : ℝ) / 5 ≤ 49 / 100) _).1
  have hsb : ∀ ε, (3 : ℝ) ≤ sieveSigma ε := fun ε =>
    (sieveClip_bounds (by norm_num : (3 : ℝ) ≤ 7 / 2) _).1
  have hp : ∀ ε, 1 < sieveRhoTwo ε * sieveSigma ε := by
    intro ε
    have hm := mul_le_mul (h2b ε) (hsb ε) (by norm_num : (0 : ℝ) ≤ 3)
      (by linarith [h2b ε] : 0 ≤ sieveRhoTwo ε)
    nlinarith
  have hprod : Continuous (fun ε => sieveRhoTwo ε * sieveSigma ε) := h2.mul hs
  have hroot : Continuous (fun ε => Real.sqrt (sieveRhoTwo ε * sieveSigma ε) +
      Real.sqrt (sieveRhoTwo ε * sieveSigma ε - 1)) :=
    (Real.continuous_sqrt.comp hprod).add (Real.continuous_sqrt.comp (hprod.sub continuous_const))
  have hL : Continuous (fun ε => sieveLeftClosed (sieveRhoTwo ε) (sieveSigma ε)) := by
    unfold sieveLeftClosed
    exact (hroot.log (fun ε => ne_of_gt (add_pos_of_pos_of_nonneg
      (Real.sqrt_pos.mpr (by linarith [hp ε])) (Real.sqrt_nonneg _)))).div
      (Real.continuous_sqrt.comp h2) (fun ε => ne_of_gt (Real.sqrt_pos.mpr (by linarith [h2b ε])))
  have hR : Continuous (fun ε => (sieveRhoOne ε)⁻¹ * stableSieveRightIntegral (sieveSigma ε)) :=
    (h1.inv₀ (fun ε => by have := h1b ε; linarith)).mul (continuous_stableSieveRightIntegral.comp hs)
  unfold stableSieveGap
  exact (hL.sub hR).sub continuous_const

/-- The exact margin gives positivity at the unperturbed point. -/
theorem stableSieveGap_zero_pos : 0 < stableSieveGap 0 := by
  have h1 : sieveRhoOne 0 = 19 / 40 := by norm_num [sieveRhoOne, sieveClip]
  have h2 : sieveRhoTwo 0 = 57 / 140 := by norm_num [sieveRhoTwo, sieveClip]
  have hs : sieveSigma 0 = 120 / 37 := by norm_num [sieveSigma, sieveClip]
  unfold stableSieveGap
  rw [h1, h2, hs, stableSieveRightIntegral_eq (by norm_num) (by norm_num)]
  have he : generalSieveEndpoint (120 / 37) = sieveEndpoint := by
    unfold generalSieveEndpoint sieveEndpoint
    norm_num
  rw [he]
  change 0 < sieveLeftClosed (57 / 140) (120 / 37) -
    (19 / 40 : ℝ)⁻¹ * (∫ u in (0 : ℝ)..sieveEndpoint, sieveRightIntegrand u) - 1 / 10 ^ 10
  have hb := sieve_right_integral_le_closed
  have hm := sieve_closed_margin
  norm_num at hb hm ⊢
  linarith

/-- The clipping agrees with the paper perturbation for small nonnegative epsilon. -/
theorem sieve_parameter_curves_eq {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1 / 1000) :
    sieveRhoOne ε = 19 / 40 - ε ∧ sieveRhoTwo ε = 57 / 140 - ε ∧
      sieveSigma ε = 120 / 37 + ε := by
  exact ⟨sieveClip_eq (by linarith) (by linarith), sieveClip_eq (by linarith) (by linarith),
    sieveClip_eq (by linarith) (by linarith)⟩

/-- Definition 6.3 still holds after a sufficiently small positive perturbation. -/
theorem sieveH_small_perturbation : ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
    SieveH (19 / 40 - ε) (57 / 140 - ε) (120 / 37 + ε) := by
  have hopen : IsOpen {ε : ℝ | 0 < stableSieveGap ε} := isOpen_lt continuous_const continuous_stableSieveGap
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds stableSieveGap_zero_pos)
  refine ⟨min δ (1 / 1000), lt_min hδ (by norm_num), ?_⟩
  intro ε hε hεsmall
  have heδ : ε < δ := hεsmall.trans_le (min_le_left _ _)
  have he1 : ε < 1 / 1000 := hεsmall.trans_le (min_le_right _ _)
  have hG : 0 < stableSieveGap ε := hball (Metric.mem_ball.mpr (by
    simpa [Real.dist_eq, abs_of_pos hε] using heδ))
  obtain ⟨h1, h2, hs⟩ := sieve_parameter_curves_eq hε.le he1
  have hσ : (3 : ℝ) ≤ 120 / 37 + ε := by linarith
  have hσ1 : (120 : ℝ) / 37 + ε ≤ 7 / 2 := by linarith
  have hρ2 : 0 < (57 : ℝ) / 140 - ε := by linarith
  have hρ1 : (19 : ℝ) / 40 - ε ≠ 0 := by linarith
  have hprod : 1 < ((57 : ℝ) / 140 - ε) * (120 / 37 + ε) := by nlinarith
  unfold stableSieveGap at hG
  rw [h1, h2, hs, stableSieveRightIntegral_eq hσ hσ1] at hG
  unfold SieveH
  rw [sieve_left_integral_eq hρ2 hprod, general_sieve_right_substitution hσ hσ1]
  have he : (1 : ℝ) / (2 * (19 / 40 - ε)) *
      (2 * ∫ u in (0 : ℝ)..generalSieveEndpoint (120 / 37 + ε), generalSieveRight (120 / 37 + ε) u) =
      (19 / 40 - ε)⁻¹ *
        (∫ u in (0 : ℝ)..generalSieveEndpoint (120 / 37 + ε), generalSieveRight (120 / 37 + ε) u) := by
    field_simp [hρ1]
  rw [he]
  linarith

/-- The perturbed parameters remain in the domain stated in Definition 6.3. -/
theorem sieve_perturbed_parameters_admissible {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 1000) :
    (1 : ℝ) / 3 < 57 / 140 - ε ∧ (57 : ℝ) / 140 - ε < 19 / 40 - ε ∧
    (19 : ℝ) / 40 - ε < 1 / 2 ∧ (3 : ℝ) < 120 / 37 + ε ∧ (120 : ℝ) / 37 + ε < 4 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

#print axioms continuous_stableSieveGap
#print axioms stableSieveGap_zero_pos
#print axioms sieve_parameter_curves_eq
#print axioms sieveH_small_perturbation
#print axioms sieve_perturbed_parameters_admissible

end LeanLab.Teravainen2016

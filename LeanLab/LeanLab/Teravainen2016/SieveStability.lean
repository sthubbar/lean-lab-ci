/-
P0076 Section 11, page 47. Continuity of the numerical sieve inequality under perturbation.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.SieveRight

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

namespace LeanLab.Teravainen2016

noncomputable def generalSieveEndpoint (σ : ℝ) : ℝ := Real.sqrt (1 - 2 / σ)
noncomputable def generalSieveRight (σ u : ℝ) : ℝ :=
  Real.log (σ * (1 - u ^ 2) - 1) / (1 - u ^ 2)

/-- Endpoints stay inside a fixed compact interval near the page 47 parameters. -/
theorem generalSieveEndpoint_bounds {σ : ℝ} (hσ : 3 ≤ σ) (hσ1 : σ ≤ 7 / 2) :
    0 < generalSieveEndpoint σ ∧ generalSieveEndpoint σ < 2 / 3 := by
  have hσ0 : 0 < σ := by linarith
  have hlow : 0 < 1 - 2 / σ := by rw [sub_pos, div_lt_one hσ0]; linarith
  have hinv : (4 : ℝ) / 7 ≤ 2 / σ := by rw [le_div_iff₀ hσ0]; linarith
  unfold generalSieveEndpoint
  exact ⟨Real.sqrt_pos.mpr hlow, (Real.sqrt_lt hlow.le (by norm_num)).mpr (by linarith)⟩

/-- The right integral substitution holds throughout the nearby parameter interval. -/
theorem general_sieve_right_substitution {σ : ℝ} (hσ : 3 ≤ σ) (hσ1 : σ ≤ 7 / 2) :
    (∫ t in (2 : ℝ)..σ, Real.log (t - 1) / (t * Real.sqrt (1 - t / σ))) =
      2 * ∫ u in (0 : ℝ)..generalSieveEndpoint σ, generalSieveRight σ u := by
  have ha := generalSieveEndpoint_bounds hσ hσ1
  have hσ0 : 0 < σ := by linarith
  have hs : 0 ≤ 1 - 2 / σ := by rw [sub_nonneg, div_le_one hσ0]; linarith
  have ha2 : generalSieveEndpoint σ ^ 2 = 1 - 2 / σ := Real.sq_sqrt hs
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => σ * (1 - u ^ 2)) (-(2 * σ * u)) u := by
    intro u
    convert (((hasDerivAt_const u 1).sub ((hasDerivAt_id u).pow 2)).const_mul σ) using 1
    · rfl
    · simp
      ring
  have hsub := integral_comp_mul_deriv_of_deriv_nonpos
    (a := 0) (b := generalSieveEndpoint σ) (f := fun u : ℝ => σ * (1 - u ^ 2))
    (f' := fun u => -(2 * σ * u))
    (g := fun t : ℝ => Real.log (t - 1) / (t * Real.sqrt (1 - t / σ)))
    (by fun_prop) (fun u _ => hd u) (by
      intro u hu
      rw [min_eq_left ha.1.le, max_eq_right ha.1.le] at hu
      nlinarith [hu.1])
  have he : (∫ u in (0 : ℝ)..generalSieveEndpoint σ,
      ((fun t : ℝ => Real.log (t - 1) / (t * Real.sqrt (1 - t / σ))) ∘
        (fun u : ℝ => σ * (1 - u ^ 2))) u * (-(2 * σ * u))) =
      -2 * ∫ u in (0 : ℝ)..generalSieveEndpoint σ, generalSieveRight σ u := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr_Ioo_of_le ha.1.le
    intro u hu
    dsimp only [Function.comp_apply]
    rw [show (1 : ℝ) - (σ * (1 - u ^ 2)) / σ = u ^ 2 by field_simp; ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hu.1]
    unfold generalSieveRight
    have hu1 : u < 1 := lt_trans hu.2 (lt_trans ha.2 (by norm_num))
    have hden : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1]
    field_simp [ne_of_gt hu.1, hden, hσ0.ne']
  have hend : σ * (1 - generalSieveEndpoint σ ^ 2) = 2 := by rw [ha2]; field_simp; ring
  rw [show σ * (1 - (0 : ℝ) ^ 2) = σ by ring, hend, he] at hsub
  rw [intervalIntegral.integral_symm (a := (2 : ℝ)) (b := σ)] at hsub
  linarith

/-- Clipping permits a global continuous representative of the nearby integral family. -/
noncomputable def sieveClip (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem sieveClip_bounds {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) :
    lo ≤ sieveClip lo hi x ∧ sieveClip lo hi x ≤ hi := by
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem sieveClip_eq {lo hi x : ℝ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    sieveClip lo hi x = x := by simp [sieveClip, min_eq_right hhi, max_eq_right hlo]

noncomputable def stableSieveRight (σ u : ℝ) : ℝ :=
  generalSieveRight (sieveClip 3 (7 / 2) σ) (sieveClip 0 (2 / 3) u)

/-- The clipped integrand is jointly continuous everywhere. -/
theorem continuous_stableSieveRight : Continuous (Function.uncurry stableSieveRight) := by
  have hsc : Continuous (fun p : ℝ × ℝ => sieveClip 3 (7 / 2) p.1) := by unfold sieveClip; fun_prop
  have huc : Continuous (fun p : ℝ × ℝ => sieveClip 0 (2 / 3) p.2) := by unfold sieveClip; fun_prop
  have hd : ∀ p : ℝ × ℝ, 0 < 1 - sieveClip 0 (2 / 3) p.2 ^ 2 := by
    intro p
    obtain ⟨h0, h1⟩ := sieveClip_bounds (by norm_num : (0 : ℝ) ≤ 2 / 3) p.2
    nlinarith
  have hy : ∀ p : ℝ × ℝ,
      0 < sieveClip 3 (7 / 2) p.1 * (1 - sieveClip 0 (2 / 3) p.2 ^ 2) - 1 := by
    intro p
    obtain ⟨h0, h1⟩ := sieveClip_bounds (by norm_num : (0 : ℝ) ≤ 2 / 3) p.2
    obtain ⟨hs0, hs1⟩ := sieveClip_bounds (by norm_num : (3 : ℝ) ≤ 7 / 2) p.1
    have hden : (5 : ℝ) / 9 ≤ 1 - sieveClip 0 (2 / 3) p.2 ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hs0 (le_trans (by norm_num) hden)
    nlinarith
  have hdc : Continuous (fun p : ℝ × ℝ => 1 - sieveClip 0 (2 / 3) p.2 ^ 2) := continuous_const.sub (huc.pow 2)
  have hyc : Continuous (fun p : ℝ × ℝ =>
      sieveClip 3 (7 / 2) p.1 * (1 - sieveClip 0 (2 / 3) p.2 ^ 2) - 1) :=
    (hsc.mul hdc).sub continuous_const
  unfold Function.uncurry stableSieveRight generalSieveRight
  exact (hyc.log (fun p => (hy p).ne')).div hdc (fun p => (hd p).ne')

/-- The clipped endpoint is continuous as a function of sigma. -/
theorem continuous_clippedSieveEndpoint :
    Continuous (fun σ : ℝ => generalSieveEndpoint (sieveClip 3 (7 / 2) σ)) := by
  have hc : Continuous (sieveClip 3 (7 / 2)) := by unfold sieveClip; fun_prop
  unfold generalSieveEndpoint
  apply Real.continuous_sqrt.comp
  apply continuous_const.sub
  exact continuous_const.div hc (fun σ => ne_of_gt (lt_of_lt_of_le (by norm_num)
    (sieveClip_bounds (by norm_num : (3 : ℝ) ≤ 7 / 2) σ).1))

noncomputable def stableSieveRightIntegral (σ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..generalSieveEndpoint (sieveClip 3 (7 / 2) σ), stableSieveRight σ u

/-- The nearby right integral family is continuous. -/
theorem continuous_stableSieveRightIntegral : Continuous stableSieveRightIntegral :=
  continuous_parametric_intervalIntegral_of_continuous continuous_stableSieveRight continuous_clippedSieveEndpoint

/-- On the parameter interval, clipping does not change the integral. -/
theorem stableSieveRightIntegral_eq {σ : ℝ} (hσ : 3 ≤ σ) (hσ1 : σ ≤ 7 / 2) :
    stableSieveRightIntegral σ = ∫ u in (0 : ℝ)..generalSieveEndpoint σ, generalSieveRight σ u := by
  unfold stableSieveRightIntegral
  rw [sieveClip_eq hσ hσ1]
  apply integral_congr_Ioo_of_le (generalSieveEndpoint_bounds hσ hσ1).1.le
  intro u hu
  unfold stableSieveRight
  rw [sieveClip_eq hσ hσ1, sieveClip_eq hu.1.le (lt_trans hu.2 (generalSieveEndpoint_bounds hσ hσ1).2).le]

#print axioms generalSieveEndpoint_bounds
#print axioms general_sieve_right_substitution
#print axioms sieveClip_bounds
#print axioms sieveClip_eq
#print axioms continuous_stableSieveRight
#print axioms continuous_clippedSieveEndpoint
#print axioms continuous_stableSieveRightIntegral
#print axioms stableSieveRightIntegral_eq

end LeanLab.Teravainen2016

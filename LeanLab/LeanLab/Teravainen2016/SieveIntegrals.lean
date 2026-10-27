/-
P0076 Definition 6.3, page 21. Integral identities for the certified sieve margin.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.SieveMargin

open MeasureTheory intervalIntegral Set
open scoped Topology

namespace LeanLab.Teravainen2016

/-- The singular left integral has an arsinh primitive after a monotone substitution. -/
theorem integral_inv_sqrt_mul_sub {x : ℝ} (hx : 1 < x) :
    (∫ t in (1 : ℝ)..x, 1 / Real.sqrt (t * (t - 1))) =
      2 * Real.log (Real.sqrt x + Real.sqrt (x - 1)) := by
  let s := Real.sqrt (x - 1)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * u) u := by
    intro u
    simpa [pow_one, mul_comm] using ((hasDerivAt_id u).pow 2).const_add 1
  have hsub := integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := s) (f := fun u : ℝ => 1 + u ^ 2) (f' := fun u => 2 * u)
    (g := fun t : ℝ => 1 / Real.sqrt (t * (t - 1)))
    (by fun_prop) (fun u _ => hd u) (by
      intro u hu
      rw [min_eq_left hs.le, max_eq_right hs.le] at hu
      linarith [hu.1])
  have he : (∫ u in (0 : ℝ)..s,
      ((fun t : ℝ => 1 / Real.sqrt (t * (t - 1))) ∘ (fun u : ℝ => 1 + u ^ 2)) u * (2 * u)) =
      ∫ u in (0 : ℝ)..s, 2 * (Real.sqrt (1 + u ^ 2))⁻¹ := by
    apply integral_congr_Ioo_of_le hs.le
    intro u hu
    dsimp only [Function.comp_apply]
    rw [show 1 + u ^ 2 - 1 = u ^ 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_pos hu.1]
    have hroot : Real.sqrt (1 + u ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp [ne_of_gt hu.1, hroot]
  have hint : IntervalIntegrable (fun u : ℝ => 2 * (Real.sqrt (1 + u ^ 2))⁻¹) volume 0 s := by
    apply Continuous.intervalIntegrable
    have hc : Continuous (fun u : ℝ => Real.sqrt (1 + u ^ 2)) := by fun_prop
    exact continuous_const.mul (hc.inv₀ (fun u => ne_of_gt (Real.sqrt_pos.mpr (by positivity))))
  have hprim : (∫ u in (0 : ℝ)..s, 2 * (Real.sqrt (1 + u ^ 2))⁻¹) = 2 * Real.arsinh s := by
    have h := integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => 2 * Real.arsinh u) (f' := fun u => 2 * (Real.sqrt (1 + u ^ 2))⁻¹)
      (a := 0) (b := s) (fun u _ => (Real.hasDerivAt_arsinh u).const_mul 2) hint
    simpa using h
  norm_num only [zero_pow, add_zero] at hsub
  rw [show 1 + s ^ 2 = x by linarith] at hsub
  rw [← hsub, he, hprim]
  rw [Real.arsinh]
  congr 2
  rw [show 1 + s ^ 2 = x by linarith]
  dsimp [s]
  ring

/-- The left side of display 6.1 equals the certified closed expression. -/
theorem sieve_left_integral_eq {ρ₂ σ : ℝ} (hρ : 0 < ρ₂) (hx : 1 < ρ₂ * σ) :
    1 / (2 * Real.sqrt ρ₂) * (∫ t in (1 : ℝ)..(ρ₂ * σ), 1 / Real.sqrt (t * (t - 1))) =
      sieveLeftClosed ρ₂ σ := by
  rw [integral_inv_sqrt_mul_sub hx]
  unfold sieveLeftClosed
  ring

#print axioms integral_inv_sqrt_mul_sub
#print axioms sieve_left_integral_eq

end LeanLab.Teravainen2016

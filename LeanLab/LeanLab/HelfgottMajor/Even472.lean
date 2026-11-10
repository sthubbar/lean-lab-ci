import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-!
The simple zero at the origin in the even character case of P0014 page 33.
The functional equation and nonvanishing at one are Mathlib theorems.
No finite critical line check or explicit prime sum formula is used.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Even472
open Complex Filter DirichletCharacter
open scoped Topology

/-- The reciprocal real Gamma factor has derivative one half at zero.
This is the local Gamma factor used in P0014 page 33, display 4.8.
-/
theorem inverse_Gamma_real_hasDerivAt_zero :
    HasDerivAt (fun s : ℂ => (Gammaℝ s)⁻¹) (1 / 2) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h := Gammaℝ_residue_zero.inv₀ (by norm_num : (2 : ℂ) ≠ 0)
  simpa [Gammaℝ, Gamma_zero, mul_inv, smul_eq_mul, mul_comm] using h

/-- The completed L function of a primitive nontrivial character is nonzero at zero.
Source P0014 page 33, the functional equation in display 4.8.
-/
theorem completed_L_zero_ne_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    completedLFunction χ 0 ≠ 0 := by
  have hp : χ⁻¹.IsPrimitive := by
    change conductor χ⁻¹ = q
    rw [conductor_inv]
    exact hprim
  have hn : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hc : completedLFunction χ⁻¹ 1 ≠ 0 := by
    intro hz
    apply LFunction_apply_one_ne_zero hn
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inl one_ne_zero), hz, zero_div]
  have hfe := hp.completedLFunction_one_sub (0 : ℂ)
  simp only [sub_zero, inv_inv] at hfe
  intro hz
  rw [hz, mul_zero] at hfe
  exact hc hfe

/-- The derivative of an even primitive nontrivial L function at zero is half its completed value.
Source P0014 page 33, the coefficient one over s in the even case after display 4.9.
-/
theorem even_L_hasDerivAt_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (heven : χ.Even) :
    HasDerivAt (LFunction χ) (completedLFunction χ 0 / 2) 0 := by
  have hq : q ≠ 1 := hχ ∘ level_one' χ
  have hd := ((differentiable_completedLFunction hχ) 0).hasDerivAt.mul
    inverse_Gamma_real_hasDerivAt_zero
  convert hd using 1
  · ext s
    rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr hq), heven.gammaFactor_def]
    rfl
  · simp [Gammaℝ, Gamma_zero]
    ring

/-- The zero at zero of an even primitive nontrivial L function is simple.
Source P0014 page 33, the even case of the Laurent expansion after display 4.9.
-/
theorem even_L_simple_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even) :
    analyticOrderAt (LFunction χ) 0 = 1 ∧ analyticOrderNatAt (LFunction χ) 0 = 1 := by
  have ha : AnalyticAt ℂ (LFunction χ) 0 := (differentiable_LFunction hχ).analyticAt 0
  have hq : q ≠ 1 := hχ ∘ level_one' χ
  have hz : LFunction χ 0 = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hq), heven.gammaFactor_def]
    simp [Gammaℝ, Gamma_zero]
  have hd : deriv (LFunction χ) 0 ≠ 0 := by
    rw [(even_L_hasDerivAt_zero q χ hχ heven).deriv]
    exact div_ne_zero (completed_L_zero_ne_zero q χ hprim hχ) (by norm_num)
  have ho := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd
  refine ⟨ho, ?_⟩
  simp [analyticOrderNatAt, ho]

/-- The actual L function factors as s times an analytic unit whose value is fixed.
Source P0014 page 33, the simple even zero in the Laurent expansion after display 4.9.
-/
theorem even_L_analytic_unit (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (LFunction χ =ᶠ[𝓝 (0 : ℂ)] fun s => s * u s) ∧
      u 0 = completedLFunction χ 0 / 2 := by
  have ha : AnalyticAt ℂ (LFunction χ) 0 := (differentiable_LFunction hχ).analyticAt 0
  obtain ⟨ho, hon⟩ := even_L_simple_zero q χ hprim hχ heven
  have hf : analyticOrderAt (LFunction χ) 0 ≠ ⊤ := by rw [ho]; simp
  obtain ⟨u, hu, hu0, heq⟩ := ha.analyticOrderAt_ne_top.mp hf
  have he : LFunction χ =ᶠ[𝓝 (0 : ℂ)] fun s => s * u s := by
    simpa only [hon, sub_zero, pow_one, smul_eq_mul] using! heq
  refine ⟨u, hu, hu0, he, ?_⟩
  have hd : deriv (LFunction χ) 0 = u 0 := by
    rw [he.deriv_eq]
    simpa only [Pi.mul_apply, id_eq, one_mul, zero_mul, add_zero] using!
      ((hasDerivAt_id (0 : ℂ)).mul hu.differentiableAt.hasDerivAt).deriv
  exact hd.symm.trans (even_L_hasDerivAt_zero q χ hχ heven).deriv

/-- In the odd primitive case the actual L function is nonzero at the origin.
Source P0014 page 33, the case kappa equal to one after display 4.9.
-/
theorem odd_L_zero_ne_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hodd : χ.Odd) :
    LFunction χ 0 ≠ 0 := by
  have hq : q ≠ 1 := hχ ∘ level_one' χ
  rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hq), hodd.gammaFactor_def]
  simpa only [zero_add, Gammaℝ_one, div_one] using completed_L_zero_ne_zero q χ hprim hχ

end LeanLab.HelfgottMajor.Even472

#print axioms LeanLab.HelfgottMajor.Even472.inverse_Gamma_real_hasDerivAt_zero
#print axioms LeanLab.HelfgottMajor.Even472.completed_L_zero_ne_zero
#print axioms LeanLab.HelfgottMajor.Even472.even_L_hasDerivAt_zero
#print axioms LeanLab.HelfgottMajor.Even472.even_L_simple_zero
#print axioms LeanLab.HelfgottMajor.Even472.even_L_analytic_unit
#print axioms LeanLab.HelfgottMajor.Even472.odd_L_zero_ne_zero

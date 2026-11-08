import LeanLab.HelfgottMajor.Continuation457
import LeanLab.HelfgottMajor.LogDeriv309

/-!
The residue scaling question for the nonzero shift branches of the assigned split.
Source P0014 pages 33 and 34, displays 4.6 and 4.7.
These are local coefficient statements. They do not refute a sealed explicit formula leaf.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Shifted457
open Complex Filter
open LeanLab.HelfgottArcs Decomp269a
open scoped Topology

/-- The scaled simple pole coefficient from the regular logarithmic derivative and Gaussian factors.
Source P0014 pages 33 and 34, retaining x to the power s from display 4.7.
-/
noncomputable def scaledCoefficient (n : ℕ) (u : ℂ → ℂ) (δ x : ℝ) : ℂ :=
  deriv (fun s : ℂ => ((n : ℂ) + s * logDeriv u s) *
    (gaussianMellin δ (s + 2) - (2 * Real.pi * Complex.I * δ) * gaussianMellin δ (s + 1)) *
      (x : ℂ) ^ s) 0

/-- The shifted Gaussian changes the constant coefficient but leaves the n log x scaling term.
Source P0014 page 33 display 4.7 and page 35 display 4.14.
-/
theorem scaled_coefficient (n : ℕ) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (δ x : ℝ) (hx : 0 < x) :
    scaledCoefficient n u δ x = logDeriv u 0 +
      n * deriv (fun s : ℂ => gaussianMellin δ (s + 2) -
        (2 * Real.pi * Complex.I * δ) * gaussianMellin δ (s + 1)) 0 +
      n * (Real.log x : ℂ) := by
  let H : ℂ → ℂ := fun s => gaussianMellin δ (s + 2) -
    (2 * Real.pi * Complex.I * δ) * gaussianMellin δ (s + 1)
  have h2 := DifferentiableAt.comp (0 : ℂ)
    (Continuation457.gaussian_mellin_differentiable δ ((0 : ℂ) + 2) (by norm_num))
    (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s + 2) 0)
  have h1 := DifferentiableAt.comp (0 : ℂ)
    (Continuation457.gaussian_mellin_differentiable δ ((0 : ℂ) + 1) (by norm_num))
    (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s + 1) 0)
  have hH : HasDerivAt H (deriv H 0) 0 := (h2.sub (h1.const_mul _)).hasDerivAt
  have hH0 : H 0 = 1 := by simpa [H] using Continuation457.shifted_first_moment δ
  have hh := (Residue309.scaled_numerator_derivative
    (fun s : ℂ => (n : ℂ) + s * logDeriv u s) H (logDeriv u 0) (deriv H 0) n 1
    (LogDeriv309.regular_logderiv_derivative n u hu hu0) hH (by simp) hH0 x hx).deriv
  simpa only [scaledCoefficient, H, mul_one] using hh

/-- The coefficient difference is exactly n log x for every real shift.
Derived scaling comparison for P0014 page 33 display 4.7.
-/
theorem coefficient_gap (n : ℕ) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (δ x : ℝ) (hx : 0 < x) :
    scaledCoefficient n u δ x - scaledCoefficient n u δ 1 = n * (Real.log x : ℂ) := by
  rw [scaled_coefficient n u hu hu0 δ x hx,
    scaled_coefficient n u hu hu0 δ 1 (by norm_num), Real.log_one]
  simp only [Complex.ofReal_zero, mul_zero, add_zero, add_sub_cancel_left]

/-- The two admissible scales force a residue budget escape for shifts of absolute value at most two.
Source P0014 pages 33 and 44. This is a local coefficient obstruction, not a zero sum estimate.
-/
theorem shifted_residue_budget_escape (n : ℕ) (hn : 0 < n) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (δ : ℝ) (hδ : |δ| ≤ 2) :
    3 * Real.log 5 + 13.347 * |δ| + 16.695 < ‖scaledCoefficient n u δ 1‖ ∨
      3 * Real.log 5 + 13.347 * |δ| + 16.695 <
        ‖scaledCoefficient n u δ (Real.exp 100)‖ := by
  have hlog : Real.log (5 : ℝ) < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at hh
    linarith
  have hB : 3 * Real.log 5 + 13.347 * |δ| + 16.695 < 50 := by linarith
  have hgap := coefficient_gap n u hu hu0 δ (Real.exp 100) (Real.exp_pos _)
  rw [Real.log_exp] at hgap
  have hnorm : ‖scaledCoefficient n u δ (Real.exp 100) - scaledCoefficient n u δ 1‖ =
      100 * (n : ℝ) := by
    rw [hgap, norm_mul]
    norm_num
    ring
  have htri := norm_sub_le (scaledCoefficient n u δ (Real.exp 100)) (scaledCoefficient n u δ 1)
  rw [hnorm] at htri
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_contra hh
  have hfirst := le_of_not_gt (not_or.mp hh).1
  have hsecond := le_of_not_gt (not_or.mp hh).2
  nlinarith

/-- The shifted Gaussian numerator agrees with the actual L function product near zero.
Source P0014 page 33 display 4.7 and page 35 display 4.14.
The analytic unit hypothesis is explicit and supplied by even_L_factorization for the actual character.
-/
theorem actual_regularized_product (L u : ℂ → ℂ) (n : ℕ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (heq : L =ᶠ[𝓝 (0 : ℂ)] fun s => s ^ n * u s) (δ : ℝ) :
    (fun t : ℝ => (t : ℂ) ^ 2 * logDeriv L (t : ℂ) * gaussianMellin δ (t : ℂ))
      =ᶠ[𝓝[>] (0 : ℝ)] fun t =>
        ((n : ℂ) + (t : ℂ) * logDeriv u (t : ℂ)) *
          (gaussianMellin δ ((t : ℂ) + 2) -
            (2 * Real.pi * Complex.I * δ) * gaussianMellin δ ((t : ℂ) + 1)) := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    change (t : ℂ) ≠ 0
    exact_mod_cast ht.ne'
  have hl : logDeriv L =ᶠ[𝓝[≠] (0 : ℂ)] logDeriv (fun s : ℂ => s ^ n * u s) :=
    (logDeriv_congr_nhds heq).filter_mono nhdsWithin_le_nhds
  filter_upwards [ht.eventually hl, ht.eventually (LogDeriv309.regular_logderiv_eq n u hu hu0),
    self_mem_nhdsWithin] with t htL htreg htpos
  change 0 < t at htpos
  have hg := Continuation457.gaussian_mellin_recurrence δ (t : ℂ) (by simpa using htpos)
  rw [← hg, ← htreg, htL]
  ring

/-- The modulo five primitive even character gives the obstruction in both assigned shift regimes.
Source P0014 pages 33 and 44. No finite critical line hypothesis or complete explicit formula is asserted.
-/
theorem mod_five_shifted_obstruction :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.Even ∧
      ∃ n : ℕ, 0 < n ∧ ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (DirichletCharacter.LFunction χ =ᶠ[𝓝 (0 : ℂ)] fun s => s ^ n * u s) ∧
        ∀ δ ∈ ({1, 2} : Set ℝ),
          3 * Real.log 5 + 13.347 * |δ| + 16.695 < ‖scaledCoefficient n u δ 1‖ ∨
            3 * Real.log 5 + 13.347 * |δ| + 16.695 <
              ‖scaledCoefficient n u δ (Real.exp 100)‖ := by
  obtain ⟨χ, hprim, hχ, heven⟩ := LogDeriv309.exists_even_primitive_mod_five
  obtain ⟨n, hn, u, hu, hu0, heq⟩ := LogDeriv309.even_L_factorization 5 (by decide) χ hχ heven
  refine ⟨χ, hprim, hχ, heven, n, hn, u, hu, hu0, heq, ?_⟩
  intro δ hδ
  apply shifted_residue_budget_escape n hn u hu hu0 δ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl <;> norm_num

end LeanLab.HelfgottMajor.Shifted457

#print axioms LeanLab.HelfgottMajor.Shifted457.scaled_coefficient
#print axioms LeanLab.HelfgottMajor.Shifted457.coefficient_gap
#print axioms LeanLab.HelfgottMajor.Shifted457.shifted_residue_budget_escape
#print axioms LeanLab.HelfgottMajor.Shifted457.actual_regularized_product
#print axioms LeanLab.HelfgottMajor.Shifted457.mod_five_shifted_obstruction

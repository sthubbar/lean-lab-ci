import LeanLab.HelfgottMajor.Shifted457
import LeanLab.HelfgottMajor.LogWeight457
import LeanLab.HelfgottMajor.Contour472
import LeanLab.HelfgottMajor.Even472

/-!
The scale term in the residue of P0014 page 33 display 4.7.
A contour error bounded by an inverse square root cannot cancel this term.
These local statements do not assert a contour identity for the prime sum.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Supply472
open Real Shifted457 MeasureTheory Contour457 Filter
open scoped Topology

/-- The local residue coefficient of the actual even primitive L function changes by log x.
Source P0014 page 33, display 4.7, retaining the scale factor at the simple even zero.
This is a local coefficient identity and asserts no prime sum contour shift.
-/
theorem even_primitive_coefficient_gap (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (DirichletCharacter.LFunction χ =ᶠ[𝓝 (0 : ℂ)] fun s => s * u s) ∧
      u 0 = DirichletCharacter.completedLFunction χ 0 / 2 ∧
      ∀ δ x : ℝ, 0 < x →
        scaledCoefficient 1 u δ x - scaledCoefficient 1 u δ 1 = (Real.log x : ℂ) := by
  obtain ⟨u, hu, hu0, heq, huv⟩ := Even472.even_L_analytic_unit q χ hprim hχ heven
  refine ⟨u, hu, hu0, heq, huv, ?_⟩
  intro δ x hx
  simpa only [Nat.cast_one, one_mul] using coefficient_gap 1 u hu hu0 δ x hx

/-- The principal logarithmic square budget follows from its pointwise analytic envelope.
CONDITIONAL ON hpoint, a stronger envelope than the printed P0014 display 4.12.
This is a sufficient square energy comparison for page 35. The printed envelope uses an absolute logarithm.
-/
theorem principal_log_weight_budget_of_pointwise
    (hpoint : ∀ t : ℝ,
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
        (1 / 2) * Real.log (t ^ 2 + 9 / 4) + 3) :
    sqrt (∫ t : ℝ, ‖principalLogWeight t‖ ^ 2) ≤ 6.01 * sqrt (2 * π) := by
  let f : ℝ → ℝ := fun t => ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖
  have hfact : f = fun t =>
      ‖principalLogWeight t * ((-1 / 2 : ℂ) + t * Complex.I)‖ := by
    ext t
    have hs : (-1 / 2 : ℂ) + t * Complex.I ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num at hh
    simp only [f, principalLogWeight, div_mul_cancel₀ _ hs]
  have hf : Continuous f := by
    rw [hfact]
    exact (LogWeight457.principalLogWeight_continuous.mul (by fun_prop)).norm
  obtain ⟨hi, hb⟩ := Contour472.contour_energy_of_log_envelope f
    hf.aestronglyMeasurable (fun _ => norm_nonneg _) hpoint
  have hsq (t : ℝ) : ‖(-1 / 2 : ℂ) + t * Complex.I‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have heq : (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) =
      fun t => f t ^ 2 / (1 / 4 + t ^ 2) := by
    ext t
    simp only [f, principalLogWeight, norm_div, div_pow, hsq]
  rw [heq]
  calc
    _ ≤ sqrt (6.01 ^ 2 * (2 * π)) := sqrt_le_sqrt hb
    _ = _ := by rw [sqrt_mul (sq_nonneg _), sqrt_sq (by norm_num : (0 : ℝ) ≤ 6.01)]

/-- The shifted residue remains unbounded after an inverse square root error is added.
Derived audit of P0014 pages 33 to 35, displays 4.7 and 4.13.
The error bound is an explicit hypothesis and no zero sum identity is assumed.
-/
theorem residue_with_decaying_error_unbounded (n : ℕ) (hn : 0 < n) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (δ : ℝ) (E : ℝ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ x : ℝ, 1 ≤ x → ‖E x‖ ≤ C / sqrt x) (B : ℝ) :
    ∃ x : ℝ, 1 ≤ x ∧ B < ‖scaledCoefficient n u δ x + E x‖ := by
  let A := scaledCoefficient n u δ 1
  let K : ℝ := max B 0 + ‖A‖ + C + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let x := Real.exp K
  have hx : 1 ≤ x := Real.one_le_exp_iff.mpr hK.le
  have hx0 : 0 < x := Real.exp_pos K
  have herror : ‖E x‖ ≤ C :=
    (hE x hx).trans (div_le_self hC (one_le_sqrt.mpr hx))
  have hgap := coefficient_gap n u hu hu0 δ x hx0
  have hxlog : Real.log x = K := Real.log_exp K
  rw [hxlog] at hgap
  have hnorm : ‖scaledCoefficient n u δ x - A‖ = (n : ℝ) * K := by
    rw [hgap, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hK.le]
  have htri := norm_le_add_norm_add (scaledCoefficient n u δ x - A) (E x)
  have heq : scaledCoefficient n u δ x - A + E x =
      (scaledCoefficient n u δ x + E x) - A := by ring
  rw [heq] at htri
  have hsub := norm_sub_le (scaledCoefficient n u δ x + E x) A
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul : K ≤ (n : ℝ) * K := le_mul_of_one_le_left hK.le hn1
  refine ⟨x, hx, ?_⟩
  rw [hnorm] at htri
  dsimp [K] at hmul
  linarith [le_max_left B 0]

/-- A regular logarithmic derivative gives an unscaled Gaussian residue for every shift.
Derived local limit from P0014 pages 33 and 34, displays 4.6 and 4.7.
Only analyticity and nonvanishing of L at zero are assumed.
-/
theorem gaussian_residue_of_nonzero (L : ℂ → ℂ) (hL : AnalyticAt ℂ L 0) (hL0 : L 0 ≠ 0)
    (δ x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => (t : ℂ) * logDeriv L (t : ℂ) *
      Decomp269a.gaussianMellin δ (t : ℂ) * (x : ℂ) ^ (t : ℂ))
      (𝓝[>] 0) (𝓝 (logDeriv L 0)) := by
  have hl : ContinuousAt (logDeriv L) 0 := (hL.deriv.div hL hL0).continuousAt
  have hG := Continuation457.regular_numerator_continuous δ
  have hp : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s) 0 :=
    continuousAt_const_cpow (by exact_mod_cast hx.ne')
  have hlim : Tendsto (fun s : ℂ => logDeriv L s *
      (Decomp269a.gaussianMellin δ (s + 2) -
        (2 * π * Complex.I * δ) * Decomp269a.gaussianMellin δ (s + 1)) *
        (x : ℂ) ^ s) (𝓝 0) (𝓝 (logDeriv L 0)) := by
    simpa only [Pi.mul_apply, zero_add, Complex.cpow_zero, mul_one,
      Continuation457.shifted_first_moment] using! ((hl.mul hG).mul hp).tendsto
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply (hlim.comp ht).congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  change 0 < t at htpos
  dsimp only [Function.comp_apply]
  rw [← Continuation457.gaussian_mellin_recurrence δ (t : ℂ) (by simpa using htpos)]
  ring

/-- The odd primitive Gaussian residue is independent of the scale x.
Source P0014 pages 33 and 34, the odd character case in display 4.7.
This is the local residue limit and does not assert the complete contour shift identity.
-/
theorem odd_gaussian_residue (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hodd : χ.Odd)
    (δ x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => (t : ℂ) * logDeriv (DirichletCharacter.LFunction χ) (t : ℂ) *
      Decomp269a.gaussianMellin δ (t : ℂ) * (x : ℂ) ^ (t : ℂ))
      (𝓝[>] 0) (𝓝 (logDeriv (DirichletCharacter.LFunction χ) 0)) := by
  exact gaussian_residue_of_nonzero _ ((DirichletCharacter.differentiable_LFunction hχ).analyticAt 0)
    (Even472.odd_L_zero_ne_zero q χ hprim hχ hodd) δ x hx

end LeanLab.HelfgottMajor.Supply472

#print axioms LeanLab.HelfgottMajor.Supply472.residue_with_decaying_error_unbounded
#print axioms LeanLab.HelfgottMajor.Supply472.principal_log_weight_budget_of_pointwise
#print axioms LeanLab.HelfgottMajor.Supply472.even_primitive_coefficient_gap
#print axioms LeanLab.HelfgottMajor.Supply472.gaussian_residue_of_nonzero
#print axioms LeanLab.HelfgottMajor.Supply472.odd_gaussian_residue

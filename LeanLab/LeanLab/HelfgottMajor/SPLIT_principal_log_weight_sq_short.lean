import LeanLab.HelfgottMajor.Decomp457b

/-!
Split of `Decomp457b.principal_log_weight_sq_short`, the short range part of the square
energy of the weight `logDeriv ζ (s) / s` on the line `s = -1/2 + it`, `|t| ≤ 2`.

The previous proof skeleton reduced the statement to the uniform pointwise bound
`‖principalLogWeight t‖ ^ 2 ≤ 5` on `|t| ≤ 2`. That pointwise bound is false: at `t = 0`
one has `ζ'(-1/2)/ζ(-1/2) ≈ 1.73583`, so `‖principalLogWeight 0‖ ^ 2 ≈ 12.0524`. The
integral statement itself is true numerically, about `12.883`.

The split here keeps the factor `1/|s|²` exact and only bounds the numerator, the
logarithmic derivative on the line `ℜ s = -1/2`, uniformly on `|t| ≤ 2` by `1.78`. This is
the sharp numerical form of display 4.12 of Helfgott, arXiv 1305.2897, page 34, for
`q = 1`, obtained from the functional equation 4.8 and 4.9 and the Dirichlet series
comparison 4.11 without the triangle inequality. The integral of `1/|s|²` over the whole
line is `2π`, and `1.78 ^ 2 * 2π < 20`.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
namespace SqShortLeaves
open Complex MeasureTheory Contour457

/-- LEAF: display 4.12 of Helfgott 1305.2897, page 34, sharpened numerically for `q = 1`
on the short range: for `s = -1/2 + it` with `|t| ≤ 2`, `|ζ'(s)/ζ(s)| ≤ 1.78`. The true
maximum is `ζ'(-1/2)/ζ(-1/2) ≈ 1.73583` at `t = 0`. Proof route: the functional equation
4.8, 4.9 gives `ζ'/ζ(s) = log 2π + (π/2) cot (π s/2) - ψ(1-s) - ζ'/ζ(1-s)`, and each term is
evaluated rigorously on `|t| ≤ 2` with its sign kept, since the triangle inequality of 4.12
loses too much. Class HARD, rigorous numerics. -/
theorem logDeriv_zeta_left_short_le (t : ℝ) (ht : |t| ≤ 2) :
    ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ≤ 1.78 := by
  sorry

/-- The weight is the logarithmic derivative divided by `s = -1/2 + it`. -/
theorem principalLogWeight_norm_sq' (t : ℝ) :
    ‖principalLogWeight t‖ ^ 2
      = ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ^ 2 / (1 / 4 + t ^ 2) := by
  have hnorm : ‖(-1 / 2 : ℂ) + t * I‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  unfold principalLogWeight
  rw [norm_div, div_pow, hnorm]

/-- The whole line integral of `1/|s|²` on `ℜ s = -1/2` is `2π`. -/
theorem integral_inv_quarter_add_sq :
    (∫ t : ℝ, (1 / 4 + t ^ 2)⁻¹) = 2 * Real.pi := by
  have h1 : (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) = fun t => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    funext t
    have : (0 : ℝ) < 1 + (2 * t) ^ 2 := by positivity
    field_simp
    ring
  rw [h1, integral_const_mul,
    Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) 2,
    integral_univ_inv_one_add_sq]
  norm_num
  ring

theorem integrable_inv_quarter_add_sq :
    Integrable (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) := by
  have h1 : (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹) = fun t => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    funext t
    have : (0 : ℝ) < 1 + (2 * t) ^ 2 := by positivity
    field_simp
    ring
  rw [h1]
  exact (integrable_inv_one_add_sq.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul 4

end SqShortLeaves

open Complex MeasureTheory SqShortLeaves in
/-- The short range square energy from the leaf: `‖w t‖² ≤ 1.78²/(1/4 + t²)` on `|t| ≤ 2`,
and the integral of the majorant over the whole line is `1.78² · 2π < 20`. -/
theorem principal_log_weight_sq_short_of_leaves :
    (∫ t in {t : ℝ | |t| ≤ 2}, ‖Contour457.principalLogWeight t‖ ^ 2) ≤ 20 := by
  classical
  have hset : ({t : ℝ | |t| ≤ 2} : Set ℝ) = Set.Icc (-2) 2 := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  have hint : Integrable (fun t : ℝ => ‖Contour457.principalLogWeight t‖ ^ 2) :=
    MeasureTheory.MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two
      (by norm_num)
  have hmaj : Integrable (fun t : ℝ => (1.78 : ℝ) ^ 2 * (1 / 4 + t ^ 2)⁻¹) :=
    integrable_inv_quarter_add_sq.const_mul _
  rw [hset]
  have hmono : (∫ t in Set.Icc (-2 : ℝ) 2, ‖Contour457.principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Icc (-2 : ℝ) 2, (1.78 : ℝ) ^ 2 * (1 / 4 + t ^ 2)⁻¹ := by
    refine MeasureTheory.setIntegral_mono_on hint.integrableOn hmaj.integrableOn
      measurableSet_Icc ?_
    intro t ht
    have habs : |t| ≤ 2 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hL := logDeriv_zeta_left_short_le t habs
    have hpos : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
    rw [principalLogWeight_norm_sq', div_eq_mul_inv]
    have h0 : (0 : ℝ) ≤ ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ := norm_nonneg _
    have hsq : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ^ 2 ≤ (1.78 : ℝ) ^ 2 :=
      pow_le_pow_left₀ h0 hL 2
    exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hpos.le)
  have hwhole : (∫ t in Set.Icc (-2 : ℝ) 2, (1.78 : ℝ) ^ 2 * (1 / 4 + t ^ 2)⁻¹)
      ≤ ∫ t : ℝ, (1.78 : ℝ) ^ 2 * (1 / 4 + t ^ 2)⁻¹ :=
    MeasureTheory.setIntegral_le_integral hmaj
      (Filter.Eventually.of_forall fun t => by positivity)
  have hval : (∫ t : ℝ, (1.78 : ℝ) ^ 2 * (1 / 4 + t ^ 2)⁻¹) = (1.78 : ℝ) ^ 2 * (2 * Real.pi) := by
    rw [integral_const_mul ((1.78 : ℝ) ^ 2) (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹),
      integral_inv_quarter_add_sq]
  rw [hval] at hwhole
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  nlinarith

end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.principal_log_weight_sq_short_of_leaves

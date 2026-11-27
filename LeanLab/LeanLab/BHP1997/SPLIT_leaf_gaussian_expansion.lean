/-
Route burst burst-20261124, session S4, KEEP GOING after unit S4-28, BHP1997, split of
`S64LowExcCharNP.leaf_gaussian_expansion` in SPLIT_leaf_gaussian_weighted_mean_value.lean.

P0069 Baker Harman Pintz 1997, page 44, proof of Lemma 29, the variant of [8] Lemma 2 with
the Gaussian weight `w(u) = exp(-u^2/4)`, Gallagher's first step, in two pieces:
* `leaf_gaussian_fubini`: `|F(u)|^2 = F(u) conj F(u)` is the double integral of
  `h(t) conj h(s) e^(iu(t-s))`, and the `u` integral moves inside by Fubini.
* `gaussian_fourier`: PROVED from Mathlib `integral_cexp_quadratic`, the Fourier transform
  `∫ w(u) e^(iux) du = 2 √π exp(-x^2)`.
* `leaf_gaussian_expansion_of_leaves`: PROVED from the two, exactly the statement of
  `leaf_gaussian_expansion`, which SPLIT_leaf_gaussian_weighted_mean_value.lean now proves
  by importing this file.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.SPLIT_leaf_plancherel_log_window

namespace LeanLab.BHP1997.S64LowExcCharNP
open Complex MeasureTheory

/-- LEAF: page 44, proof of Lemma 29, the variant of [8] Lemma 2, expansion of the square
and Fubini, class MEDIUM. P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2",
Gallagher's first step: with `F(u) = ∫_{-T}^{T} h(t) e^(itu) dt`,
`|F(u)|^2 = ∫∫ h(t) conj h(s) e^(iu(t-s)) dt ds`, and the integral over `u ∈ ℝ` against
`w(u) = exp(-u^2/4)` moves inside the double integral, the integrand being bounded by
`w(u) |h(t)| |h(s)|`, integrable on `ℝ × [-T, T]^2`. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gaussian_fubini (T : ℝ) (hT : 0 ≤ T) (h : ℝ → ℂ) (hh : Continuous h) :
    (((∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
        ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T, h t * (starRingEnd ℂ) (h s) *
        ∫ u : ℝ, ((Real.exp (-(1 / 4) * u ^ 2) : ℝ) : ℂ) *
          cexp ((u : ℂ) * (((t - s : ℝ) : ℂ) * I)) := by
  sorry

/-- Standard analysis, the Fourier transform of the Gaussian weight of page 44:
`∫_ℝ exp(-u^2/4) e^(iux) du = 2 √π exp(-x^2)`, from Mathlib `integral_cexp_quadratic`. -/
theorem gaussian_fourier (x : ℝ) :
    ∫ u : ℝ, ((Real.exp (-(1 / 4) * u ^ 2) : ℝ) : ℂ) * cexp ((u : ℂ) * ((x : ℂ) * I)) =
      ((2 * Real.sqrt Real.pi * Real.exp (-x ^ 2) : ℝ) : ℂ) := by
  have hq := integral_cexp_quadratic (b := -(1 / 4 : ℂ)) (by norm_num) ((x : ℂ) * I) 0
  have hfun : (fun u : ℝ => ((Real.exp (-(1 / 4) * u ^ 2) : ℝ) : ℂ) *
      cexp ((u : ℂ) * ((x : ℂ) * I))) =
      fun u : ℝ => cexp (-(1 / 4 : ℂ) * (u : ℂ) ^ 2 + (x : ℂ) * I * u + 0) := by
    funext u
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun, hq]
  have h1 : (Real.pi : ℂ) / -(-(1 / 4 : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (0 : ℂ) - ((x : ℂ) * I) ^ 2 / (4 * -(1 / 4 : ℂ)) = ((-x ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, I_sq]
    push_cast
    ring
  have h3 : ((4 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((2 * Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h1, h2, h3, ← Complex.ofReal_exp]
  push_cast
  ring

/-- Page 44, proof of Lemma 29: Gallagher's expansion with the Gaussian weight, PROVED from
`leaf_gaussian_fubini` and `gaussian_fourier`, exactly the statement of
`leaf_gaussian_expansion`. -/
theorem leaf_gaussian_expansion_of_leaves (T : ℝ) (hT : 0 ≤ T) (h : ℝ → ℂ)
    (hh : Continuous h) :
    (((∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
        ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T,
        h t * (starRingEnd ℂ) (h s) *
          (((2 * Real.sqrt Real.pi * Real.exp (-(t - s) ^ 2) : ℝ)) : ℂ) := by
  rw [leaf_gaussian_fubini T hT h hh]
  apply intervalIntegral.integral_congr
  intro t _
  apply intervalIntegral.integral_congr
  intro s _
  beta_reduce
  rw [gaussian_fourier (t - s)]

end LeanLab.BHP1997.S64LowExcCharNP

#print axioms LeanLab.BHP1997.S64LowExcCharNP.gaussian_fourier
#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gaussian_expansion_of_leaves

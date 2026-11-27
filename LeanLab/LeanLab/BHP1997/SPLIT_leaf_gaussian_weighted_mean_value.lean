/-
Route burst burst-20261124, session S4, KEEP GOING after unit S4-28, BHP1997, split of
`S64LowExcCharNP.leaf_gaussian_weighted_mean_value` in SPLIT_leaf_plancherel_log_window.lean.

P0069 Baker Harman Pintz 1997, page 44, proof of Lemma 29, the variant of [8] Lemma 2 with
the Gaussian weight `w(u) = exp(-u^2/4)`. Gallagher's argument has two steps:
* `leaf_gaussian_expansion`: expanding `|F(u)|^2 = F(u) conj F(u)` and integrating in `u`
  first, the weighted mean value is the double integral of `h(t) conj h(s)` against the
  Fourier transform of `w`, which is `2 √π exp(-(t-s)^2)`. Fubini and the Gaussian integral.
* `leaf_gaussian_kernel_schur`: the double integral is at most `2π ∫ |h|^2`, by
  `|h(t) h(s)| ≤ (|h(t)|^2 + |h(s)|^2)/2` and `∫_ℝ 2 √π exp(-x^2) dx = 2π`.
* `leaf_gaussian_weighted_mean_value_of_leaves`: PROVED from the two leaves with `K = 2π`.
`leaf_gaussian_weighted_mean_value_split_twin` checks the exact statement of the earlier leaf.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.SPLIT_leaf_plancherel_log_window

namespace LeanLab.BHP1997.S64LowExcCharNP
open Complex MeasureTheory

/-- LEAF: page 44, proof of Lemma 29, the variant of [8] Lemma 2, expansion of the square,
class MEDIUM. P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2", Gallagher's
first step: with `w(u) = exp(-u^2/4)` and `F(u) = ∫_{-T}^{T} h(t) e^(itu) dt`,
`∫_ℝ w(u) |F(u)|^2 du = ∫∫ h(t) conj h(s) ŵ(t - s) dt ds` with
`ŵ(x) = ∫_ℝ w(u) e^(ixu) du = 2 √π exp(-x^2)`, by Fubini and the Gaussian integral.
CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gaussian_expansion (T : ℝ) (hT : 0 ≤ T) (h : ℝ → ℂ) (hh : Continuous h) :
    (((∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
        ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ t in (-T)..T, ∫ s in (-T)..T,
        h t * (starRingEnd ℂ) (h s) *
          (((2 * Real.sqrt Real.pi * Real.exp (-(t - s) ^ 2) : ℝ)) : ℂ) := by
  sorry

/-- LEAF: page 44, proof of Lemma 29, the variant of [8] Lemma 2, the kernel bound,
class MEDIUM. P0069 Baker Harman Pintz 1997, "By a variant of [8], Lemma 2", Gallagher's
second step: the double integral against the positive kernel `2 √π exp(-(t-s)^2)` is at
most `2π ∫_{-T}^{T} |h|^2`, by `|h(t) h(s)| ≤ (|h(t)|^2 + |h(s)|^2)/2`, symmetry in `t, s`
and `∫_ℝ 2 √π exp(-x^2) dx = 2π`. CITED [8] Lemma 2, Gallagher 1970. -/
theorem leaf_gaussian_kernel_schur (T : ℝ) (hT : 0 ≤ T) (h : ℝ → ℂ) (hh : Continuous h) :
    ‖∫ t in (-T)..T, ∫ s in (-T)..T,
        h t * (starRingEnd ℂ) (h s) *
          (((2 * Real.sqrt Real.pi * Real.exp (-(t - s) ^ 2) : ℝ)) : ℂ)‖ ≤
      2 * Real.pi * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
  sorry

/-- Page 44, proof of Lemma 29: the Gaussian weighted variant of [8] Lemma 2, PROVED from
`leaf_gaussian_expansion` and `leaf_gaussian_kernel_schur` with `K = 2π`: the weighted
mean value is a real number at most the modulus of the double integral. -/
theorem leaf_gaussian_weighted_mean_value_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ h : ℝ → ℂ, Continuous h →
      ∫ u : ℝ, Real.exp (-(1 / 4) * u ^ 2) *
          ‖∫ t in (-T)..T, h t * cexp ((u : ℂ) * ((t : ℂ) * I))‖ ^ 2 ≤
        K * ∫ t in (-T)..T, ‖h t‖ ^ 2 := by
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  intro T hT h hh
  have hA := leaf_gaussian_expansion T hT h hh
  have hB := leaf_gaussian_kernel_schur T hT h hh
  rw [← hA, Complex.norm_real, Real.norm_eq_abs] at hB
  exact (le_abs_self _).trans hB

/-- The split closes exactly the statement of `leaf_gaussian_weighted_mean_value`. -/
theorem leaf_gaussian_weighted_mean_value_split_twin :
    type_of% @leaf_gaussian_weighted_mean_value :=
  leaf_gaussian_weighted_mean_value_of_leaves

end LeanLab.BHP1997.S64LowExcCharNP

#print axioms LeanLab.BHP1997.S64LowExcCharNP.leaf_gaussian_weighted_mean_value_of_leaves

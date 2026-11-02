import LeanLab.ChirreHagen2025.ZeroBounds122
import Mathlib

/-!
Decomposition of P0075 Lemma 2.2 part 1, page 3.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.DecompJ966

open LeanLab.ChirreHagen2025.ZeroBounds122
open Real Complex

/-- LEAF sorry. P0075 page 3, equation 2.4, fractional decomposition of zeta(s). -/
theorem leaf_eq_2_4 (s : ℂ) (hs : s.re > 1 / 2) :
    (deriv riemannZeta s / riemannZeta s).re =
    (∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ z.re = 1 / 2},
      (analyticOrderNatAt riemannZeta ρ : ℝ) * (s.re - 1 / 2) /
      ((s.re - 1 / 2) ^ 2 + (s.im - (ρ : ℂ).im) ^ 2)) -
    (1 / 2 * (deriv (fun z => Complex.Gamma (z / 2 + 1)) s / Complex.Gamma (s / 2 + 1)).re) +
    1 - Real.log Real.pi / 2 + (s.re - 1) / ((s.re - 1) ^ 2 + s.im ^ 2) := by
  sorry

/-- LEAF sorry. P0075 page 3, bound on Gamma'/Gamma real part. -/
theorem leaf_gamma_bound (s : ℂ) (h_re : s.re ≥ 0) (h_im : s.im ≠ 0) :
    (deriv (fun z => Complex.Gamma (z / 2 + 1)) s / Complex.Gamma (s / 2 + 1)).re ≤
    Real.log |s.im| - Real.log 2 + (s.re + 2) ^ 2 / (2 * s.im ^ 2) := by
  sorry

/-- LEAF sorry. P0075 page 3, equation 2.5. -/
theorem leaf_eq_2_5 (hRH : RiemannHypothesis) (s : ℂ) (h_re : s.re > 1 / 2) (h_im : s.im ≠ 0) :
    (∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ z.re = 1 / 2},
      (analyticOrderNatAt riemannZeta ρ : ℝ) * (s.re - 1 / 2) /
      ((s.re - 1 / 2) ^ 2 + (s.im - (ρ : ℂ).im) ^ 2)) ≤
    (deriv riemannZeta s / riemannZeta s).re +
    Real.log |s.im| / 2 - Real.log (2 * Real.pi) / 2 +
    (s.re + 2) ^ 2 / (4 * s.im ^ 2) - (s.re - 1) / ((s.re - 1) ^ 2 + s.im ^ 2) := by
  sorry

/-- LEAF sorry. P0075 page 3, text after equation (2.5), bound on zeta'/zeta on the line 1/sqrt(6)+1/2. -/
theorem leaf_zeta_deriv_bound_6 (t : ℝ) (ht : 4 ≤ |t|) :
    (deriv riemannZeta (1 / Real.sqrt 6 + 1 / 2 + t * Complex.I) /
     riemannZeta (1 / Real.sqrt 6 + 1 / 2 + t * Complex.I)).re ≤ 0.1739 := by
  sorry

/-- LEAF sorry. P0075 page 3, equation 2.2, combine bounds to prove Lemma 2.2 part 1. -/
theorem leaf_combine_bounds (hRH : RiemannHypothesis) (t : ℝ) (ht : 4 ≤ |t|) :
    Summable (zeroKernel 6 t) ∧
    (∑' ρ, zeroKernel 6 t ρ) ≤ Real.log |t| / (2 * Real.sqrt 6) := by
  sorry

/-- P0075 Lemma 2.2 part 1 assembled. -/
theorem lemma2_2_part1_assembled : lemma2_2_part1 := by
  intro hRH t ht
  exact leaf_combine_bounds hRH t ht

end LeanLab.ChirreHagen2025.DecompJ966

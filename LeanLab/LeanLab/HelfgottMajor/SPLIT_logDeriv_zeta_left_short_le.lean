import Mathlib
import LeanLab.HelfgottMajor.SPLIT_S3_digamma_binet_three_halves_le

/-!
Split of `SqShortLeaves.logDeriv_zeta_left_short_le` in
`LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_short`, burst 20261124 S4.

The target is `‖ζ'/ζ(-1/2 + it)‖ ≤ 1.78` for `|t| ≤ 2`. Helfgott, arXiv 1305.2897, page 33
and 34, estimates `L'/L` on `ℜ s = -1/2` from the functional equation 4.8 with 4.9, the
Binet type bound 4.10 for `ψ` on `ℜ z = 3/2`, and the Dirichlet series 4.11 at `1 - s`.
Here, with `z = 3/2 - it = 1 - s`:

* the functional equation in logarithmic derivative form, 4.8 with 4.9 for `q = 1`, is
  Mathlib's `logDeriv_riemannZeta_one_sub`, and `-ζ'/ζ(z)` is the von Mangoldt Dirichlet series
  by Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`; both are proved inputs, so
  `ζ'/ζ(s) = L(Λ, z) + log 2π - ψ(z) + (π/2) tan(π z / 2)` is proved below;
* LEAF `digamma_binet_three_halves_le` is display 4.10 in its intermediate form,
  `ψ(z) = log z - 1/(2z) + O*(1/27)` for `ℜ z = 3/2`;
* LEAF `logDeriv_zeta_left_short_main_le` is the rigorous numerical evaluation of the remaining
  elementary expression plus the Dirichlet series, with signs kept, since the triangle
  inequality of 4.12 loses too much. Its numerical maximum over `|t| ≤ 2` is about `1.70018`
  at `t = 0`, against the allowed `1.78 - 1/27 ≈ 1.74296`.

The assembly `logDeriv_zeta_left_short_le_of_leaves` has no sorry of its own.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
namespace SqShortLeftLeaves
open Complex
open scoped Real

/-- LEAF: display 4.10 of Helfgott 1305.2897, page 34, intermediate line: for `ℜ z = 3/2`,
`ψ(z) = log z - 1/(2z) + O*(1/27)`, from Binet's second formula `OLBC10 (5.9.15)`,
`|t² + z²| ≥ 9/4`, and `∫₀^∞ t dt / (e^{2πt} - 1) = Γ(2) ζ(2) / (2π)² = 1/24`.
Class MEDIUM: needs Binet's integral for `digamma`, not in Mathlib. -/
theorem digamma_binet_three_halves_le (z : ℂ) (hz : z.re = 3 / 2) :
    ‖digamma z - (Complex.log z - 1 / (2 * z))‖ ≤ 1 / 27 :=
  BinetS3.digamma_binet_three_halves_le_split z hz

/-- LEAF: the numerical core of display 4.12 of Helfgott 1305.2897, page 34, for `q = 1` on
the short range, sharpened by keeping signs: for `z = 3/2 - it` with `|t| ≤ 2`, the von
Mangoldt Dirichlet series 4.11 at `z` plus `log 2π - log z + 1/(2z) + (π/2) tan(π z / 2)`,
the elementary part of 4.8, 4.9 and 4.10, has norm at most `1.78 - 1/27`. The numerical
maximum is about `1.70018` at `t = 0`. Class HARD, rigorous numerics. -/
theorem logDeriv_zeta_left_short_main_le (t : ℝ) (ht : |t| ≤ 2) :
    ‖LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        ((3 / 2 : ℂ) - t * I) + Complex.log (2 * (π : ℂ)) - Complex.log ((3 / 2 : ℂ) - t * I)
        + 1 / (2 * ((3 / 2 : ℂ) - t * I))
        + (π : ℂ) / 2 * Complex.tan ((π : ℂ) * ((3 / 2 : ℂ) - t * I) / 2)‖ ≤ 1.78 - 1 / 27 := by
  sorry

/-- Displays 4.8, 4.9 and 4.11 of Helfgott 1305.2897 for `q = 1`, proved from Mathlib:
`ζ'/ζ(-1/2 + it) = L(Λ, 3/2 - it) + log 2π - ψ(3/2 - it) + (π/2) tan(π (3/2 - it) / 2)`. -/
theorem logDeriv_zeta_left_eq (t : ℝ) :
    logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I) =
      LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((3 / 2 : ℂ) - t * I) + Complex.log (2 * (π : ℂ)) - digamma ((3 / 2 : ℂ) - t * I)
        + (π : ℂ) / 2 * Complex.tan ((π : ℂ) * ((3 / 2 : ℂ) - t * I) / 2) := by
  set z : ℂ := (3 / 2 : ℂ) - t * I with hzdef
  have hzre : z.re = 3 / 2 := by simp [hzdef]
  have hz1 : (1 : ℝ) < z.re := by rw [hzre]; norm_num
  have hint : ∀ n : ℤ, z ≠ n := by
    intro n h
    have h2 := congrArg Complex.re h
    rw [hzre] at h2
    simp at h2
    have h3 : (2 : ℝ) * n = 3 := by linarith
    have h4 : (2 : ℤ) * n = 3 := by exact_mod_cast h3
    omega
  have hzeta : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz1
  have hFE := logDeriv_riemannZeta_one_sub hint hzeta
  have hs : (1 : ℂ) - z = (-1 / 2 : ℂ) + t * I := by rw [hzdef]; ring
  rw [hs] at hFE
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz1
  have hLD : logDeriv riemannZeta z = -LSeries (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) z := by
    rw [logDeriv_apply]
    rw [show (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) =
      (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) from rfl]
    have : LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) z
        = -deriv riemannZeta z / riemannZeta z := hL
    rw [this, neg_div, neg_neg]
  rw [hLD] at hFE
  linear_combination hFE

/-- `logDeriv_zeta_left_short_le` from the two leaves. -/
theorem logDeriv_zeta_left_short_le_of_leaves (t : ℝ) (ht : |t| ≤ 2) :
    ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * I)‖ ≤ 1.78 := by
  set z : ℂ := (3 / 2 : ℂ) - t * I with hzdef
  have hzre : z.re = 3 / 2 := by simp [hzdef]
  have hB := digamma_binet_three_halves_le z hzre
  have hM := logDeriv_zeta_left_short_main_le t ht
  rw [logDeriv_zeta_left_eq t]
  have hsplit : LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) z
        + Complex.log (2 * (π : ℂ)) - digamma z + (π : ℂ) / 2 * Complex.tan ((π : ℂ) * z / 2)
      = (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) z
          + Complex.log (2 * (π : ℂ)) - Complex.log z + 1 / (2 * z) + (π : ℂ) / 2 * Complex.tan ((π : ℂ) * z / 2))
        - (digamma z - (Complex.log z - 1 / (2 * z))) := by ring
  rw [hsplit]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ (1.78 - 1 / 27) + 1 / 27 := add_le_add hM hB
    _ = 1.78 := by norm_num

end SqShortLeftLeaves
end LeanLab.HelfgottMajor.Decomp457b

#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.digamma_binet_three_halves_le
#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.logDeriv_zeta_left_eq
#print axioms LeanLab.HelfgottMajor.Decomp457b.SqShortLeftLeaves.logDeriv_zeta_left_short_le_of_leaves

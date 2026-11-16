import Mathlib

/-!
Boundary equalities in Rademacher 1959, printed pages 197 and 198.
These verify the Gamma quotient used before Theorem 3.
They do not provide interpolation inside the strip.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.DERZ1997.GammaRatio623
open Complex
open scoped ComplexConjugate

/-- The right boundary equality for the quotient in Rademacher Lemma 1.
Printed page 197, display 5.2 and the following right boundary calculation.
-/
theorem gamma_ratio_right623 {Q : ℝ} (hQ : 0 ≤ Q) (t : ℝ) :
    ‖Gamma (((Q + 1 / 2 : ℝ) : ℂ) / 2 - (t : ℂ) * I / 2) /
      Gamma (((Q + 1 / 2 : ℝ) : ℂ) / 2 + (t : ℂ) * I / 2)‖ = 1 := by
  let z : ℂ := ((Q + 1 / 2 : ℝ) : ℂ) / 2 + (t : ℂ) * I / 2
  have hz : 0 < z.re := by dsimp [z]; simp; linarith
  have hconj : ((Q + 1 / 2 : ℝ) : ℂ) / 2 - (t : ℂ) * I / 2 = conj z := by
    apply Complex.ext <;> simp only [conj_re, conj_im] <;> norm_num [z]
  rw [hconj, Gamma_conj, norm_div, norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos hz))

/-- The left boundary equality from the Gamma recurrence.
Rademacher printed page 197, display 5.2, before its final norm comparison.
The removable pole case at Q equal to one half and t equal to zero is included.
-/
theorem gamma_ratio_left623 {Q : ℝ} (hQ : 0 ≤ Q) (t : ℝ) :
    ‖Gamma (((Q + 3 / 2 : ℝ) : ℂ) / 2 - (t : ℂ) * I / 2) /
      Gamma (((Q - 1 / 2 : ℝ) : ℂ) / 2 + (t : ℂ) * I / 2)‖ =
      ‖((Q - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ / 2 := by
  let z : ℂ := ((Q - 1 / 2 : ℝ) : ℂ) / 2 + (t : ℂ) * I / 2
  have hnum : ((Q + 3 / 2 : ℝ) : ℂ) / 2 - (t : ℂ) * I / 2 = conj z + 1 := by
    apply Complex.ext <;>
      simp only [add_re, add_im, conj_re, conj_im, one_re, one_im] <;>
      norm_num [z]; ring
  have hden : ((Q - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I = 2 * z := by dsimp [z]; ring
  rw [hnum, hden]
  change ‖Gamma (conj z + 1) / Gamma z‖ = ‖2 * z‖ / 2
  by_cases hz : z = 0
  · simp [hz, Gamma_zero]
  have hΓ : Gamma z ≠ 0 := by
    apply Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    have hzre : z.re = (Q - 1 / 2) / 2 := by dsimp [z]; simp
    rw [hzre] at hre
    simp only [neg_re, natCast_re] at hre
    have hn0 : n = 0 := by
      by_contra hh
      have hpos : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hh
      linarith
    subst n
    exact hz (by simpa using hn)
  rw [Gamma_add_one _ (by simpa using hz), Gamma_conj, norm_div, norm_mul,
    norm_conj, norm_conj, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hΓ), norm_mul]
  norm_num

/-- The left boundary inequality for Rademacher Lemma 1.
Printed page 197, display 5.2, with the final comparison included.
-/
theorem gamma_ratio_left_bound623 {Q : ℝ} (hQ : 0 ≤ Q) (t : ℝ) :
    ‖Gamma (((Q + 3 / 2 : ℝ) : ℂ) / 2 - (t : ℂ) * I / 2) /
      Gamma (((Q - 1 / 2 : ℝ) : ℂ) / 2 + (t : ℂ) * I / 2)‖ ≤
      ‖((Q + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ / 2 := by
  rw [gamma_ratio_left623 hQ t]
  apply div_le_div_of_nonneg_right ?_ (by norm_num)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, I_im, mul_zero, sub_zero, add_zero,
    add_im, mul_im, mul_one, zero_add]
  nlinarith

end LeanLab.DERZ1997.GammaRatio623

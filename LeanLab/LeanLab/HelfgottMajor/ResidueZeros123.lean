import LeanLab.HelfgottMajor.SPLIT_residue_log_derivative_bound
import LeanLab.HelfgottMajor.Residue123

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p5, a repair of the rejected p4 branch.
P0014 Helfgott, Major arcs for Goldbach's problem, pages 36, 37 and 44: the bound of display
4.23 on the L'/L part of the residue R of Lemma 4.1, by the paper's own route through
Lemma 4.2, whose hypothesis is that the nontrivial zeros of L(s, χ) with abs Im at most 5/8
lie on the critical line. In the proof of Proposition 4.6 that hypothesis is at hand, because
the zeros are on the line up to height T and T is at least 100.

The lab leaves SplitGaussian123.residue_log_derivative_bound and
SplitGaussian123.log_derivative_norm_le state the same bounds with NO zero hypothesis, which the
paper does not prove; that is a recorded QUESTION. The theorems here carry the hypothesis and
are PROVED from Residue123, CONDITIONAL ON the one LEAF PolyaVinogradov123.polya_vinogradov_4_20,
with the arithmetic of page 37 taken from SPLIT_residue_log_derivative_bound, where it is PROVED.
No definition is made in this file. Lemma 4.1 itself enters as the lab LEAF
SplitGaussian123.lemma_4_1_gaussian, unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ResidueZeros123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- PROVED, CONDITIONAL ON the LEAF PolyaVinogradov123.polya_vinogradov_4_20. P0014 pages 36
and 37, the display before 4.23: for χ primitive and nontrivial whose zeros with abs Im at
most 5/8 lie on the critical line, abs of log(2π/q) + γ − L'(1, χ)/L(1, χ) is at most
3 log q + 15.289. The triangle inequality with Lemma 4.2 and display 4.21 for the quotient,
and the arithmetic of page 37 for the scalar term. -/
theorem residue_log_derivative_bound_of_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      3 * log q + 15.289 := by
  have h3 := three_le_conductor χ hχ hq
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h3
  have hscal := log_two_pi_div_add_gamma_abs_le (q : ℝ) hq3
  have hquot := Residue123.log_derivative_norm_le_of_zeros χ hχ hq hzeros
  have hconst := page37_constant_budget
  refine le_trans (norm_sub_le _ _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- PROVED, CONDITIONAL ON the LEAF PolyaVinogradov123.polya_vinogradov_4_20. P0014 display
4.23, page 37, with η♥(0) equal to 1, under the zero hypothesis of Lemma 4.2: the main part of
R has norm at most 3 log q + 15.289, the trivial character giving log 2π, which is below
15.289 as the paper notes. -/
theorem residueMain_bound_of_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖residueMain χ‖ ≤ 3 * log q + 15.289 := by
  unfold residueMain
  by_cases hq : q = 1
  · subst hq
    rw [if_pos rfl, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one, log_one,
      abs_of_nonneg (log_nonneg (by nlinarith [pi_gt_three]))]
    have h := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * π)
    nlinarith [pi_lt_four]
  · rw [if_neg hq]
    exact residue_log_derivative_bound_of_zeros χ hχ hq hzeros

/-- PROVED from the lab LEAF SplitGaussian123.lemma_4_1_gaussian and residueMain_bound_of_zeros.
P0014 page 44, in the proof of Proposition 4.6: with η♥(0) equal to 1 and the norms of display
4.42, display 4.23 and c0_gauss give abs R at most 3 log q + 13.347 abs δ + 16.695, and the
repaired norm bound Lemma41Terms.repaired gives the contour factor 1 + 6 abs δ. The zero
hypothesis up to height T, T at least 100, is passed to Lemma 4.2 at height 5/8. -/
theorem explicit_formula_of_pieces_of_zeros (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hz58 : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2 :=
    fun s h0 h1 h2 h3 => hzeros s h0 h1 h2 (by linarith)
  obtain ⟨c, hc, hE⟩ := lemma_4_1_gaussian x hx q χ hχ δ T hT
  refine ⟨residueMain χ + c, ?_, ?_⟩
  · have h1 := residueMain_bound_of_zeros χ hχ hz58
    have h2 := Lemma41Terms.c0_gauss (abs_nonneg δ)
    calc ‖residueMain χ + c‖ ≤ ‖residueMain χ‖ + ‖c‖ := norm_add_le _ _
      _ ≤ _ := by linarith [abs_nonneg δ]
  · refine hE.trans ?_
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have hl : 0 ≤ log (q : ℝ) + 6.01 := by linarith [log_nonneg hq1]
    have hr := Lemma41Terms.repaired (abs_nonneg δ)
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg x)
    exact mul_le_mul_of_nonneg_left hr hl

end LeanLab.HelfgottMajor.ResidueZeros123

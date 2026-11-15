import LeanLab.HelfgottMajor.Lemma41Leaf123
import LeanLab.HelfgottMajor.SplitGaussian123
import LeanLab.HelfgottMajor.MiddleSlack123

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p6, built on p5.
P0014 Helfgott, Major arcs for Goldbach's problem, Proposition 4.6, pages 43 and 44, display
4.43, proved from the CORRECTED Lemma 4.1 of Lemma41Leaf123 in place of the printed one, which
is SUSPECTED FALSE for even primitive characters with q above 1.

The corrected residue carries log x. It is paid by two units of proved slack in the bound for
the zeros up to T, MiddleSlack123.middle_mass_bound_slack, since log x is at most 2 sqrt x for
x at least 1. The conclusion is display 4.43 exactly as Decomp123.gaussian_explicit_estimate
states it, with the recorded factor 6 repair. No definition is made in this file.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Lemma41Corrected123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- PROVED, CONDITIONAL ON the LEAF PolyaVinogradov123.polya_vinogradov_4_20. P0014 display
4.23, page 37, with η♥(0) equal to 1, under the zero hypothesis of Lemma 4.2, for the main part
of the corrected residue: its norm is at most 3 log q + 15.289. The conjugate does not change
the norm. -/
theorem residue_main_conj_bound_of_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2) :
    ‖(if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
        ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
          (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
            DirichletCharacter.LFunction χ 1))‖ ≤ 3 * log q + 15.289 := by
  by_cases hq : q = 1
  · subst hq
    rw [if_pos rfl, Complex.norm_real, Real.norm_eq_abs, Nat.cast_one, log_one,
      abs_of_nonneg (log_nonneg (by nlinarith [pi_gt_three]))]
    have h := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * π)
    nlinarith [pi_lt_four]
  · rw [if_neg hq]
    have hconj : ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
        (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
          DirichletCharacter.LFunction χ 1) =
        (starRingEnd ℂ) (((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
          deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [hconj, Complex.norm_conj]
    exact ResidueZeros123.residue_log_derivative_bound_of_zeros χ hχ hq hzeros

/-- PROVED from the LEAF Lemma41Leaf123.lemma_4_1_gaussian_corrected and Lemma 4.2. P0014 page
44, in the proof of Proposition 4.6, in CORRECTED form: the explicit formula with residue
abs R at most 3 log q + 13.347 abs δ + 16.695 + log x and contour error
(log q + 6.01)(1 + 6 abs δ) x^(-1/2), the factor 6 being the recorded repair F-5032. The
printed budget has no log x. -/
theorem explicit_formula_remainder_corrected (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 + log x ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  classical
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hz58 : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2 :=
    fun s h0 h1 h2 h3 => hzeros s h0 h1 h2 (by linarith)
  obtain ⟨c, hc, hE⟩ := Lemma41Leaf123.lemma_4_1_gaussian_corrected x hx q χ hχ δ T hT
  refine ⟨_, ?_, hE.trans ?_⟩
  · have h1 := residue_main_conj_bound_of_zeros χ hχ hz58
    have h2 := Lemma41Terms.c0_gauss (abs_nonneg δ)
    have h0 : 0 ≤ log x := log_nonneg hx
    have h3 : ‖(if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0)‖ ≤ log x := by
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      · simpa using h0
    refine (norm_add_le _ _).trans ?_
    have h4 := norm_add_le
      (if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
        ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
          (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
            DirichletCharacter.LFunction χ 1))
      (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0)
    linarith [abs_nonneg δ]
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have hl : 0 ≤ log (q : ℝ) + 6.01 := by linarith [log_nonneg hq1]
    have hr := Lemma41Terms.repaired (abs_nonneg δ)
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg x)
    exact mul_le_mul_of_nonneg_left hr hl

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count. P0014 Lemma 4.4, display 4.29 on
page 39, as applied on page 43, with two units of slack in the coefficient of sqrt x, from
MiddleSlack123.middle_mass_bound_slack. The slack pays for the log x of the corrected
Lemma 4.1. -/
theorem low_zero_bound_slack (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38 - 2) * sqrt x := by
  apply low_zero_bound_of_mass χ δ x T _ (by linarith) hzeros
  rw [mass_split χ δ T]
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hv := very_low_mass_bound q χ hχ δ T hT1 hzeros
  have hm := MiddleSlack123.middle_mass_bound_slack q χ hχ δ T hT100 hzeros
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hlogqT : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have ha := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0_log
    (mul_nonneg (sqrt_nonneg T) hlogqT)
  have hb := mul_le_mul_of_nonneg_right Sec45.coef_sqrtT0 (sqrt_nonneg T)
  obtain ⟨hc, hd⟩ := Sec45.coef_logq
  nlinarith

/-- PROVED. P0014 pages 43 and 44, the triangle inequality and arithmetic that combine
Lemmas 4.1, 4.4 and 4.5 into display 4.43, with the CORRECTED inputs: the residue budget has
the log x of the corrected Lemma 4.1, and the low zero bound has two units of slack on sqrt x.
The two cancel because log x is at most 2 sqrt x for x at least 1. The conclusion is display
4.43 as in SplitGaussian123.assembly_of_components. -/
theorem assembly_of_components_corrected (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hformula : ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 + log x ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x)
    (hL : ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38 - 2) * sqrt x)
    (hH : ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x := by
  obtain ⟨R, hR, hE⟩ := hformula
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hbudget := contour_residue_budget (q : ℝ) |δ| x hx (abs_nonneg δ)
  have hlogx : log x ≤ 2 * sqrt x := by
    have h := log_le_sub_one_of_pos hs0
    rw [log_sqrt hx0.le] at h
    linarith
  have htri : ‖Schi etaHeart χ δ x -
      (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ +
        ‖lowZeros χ δ x T‖ + ‖highZeros χ δ x T‖ + ‖R‖ := by
    calc
      _ = ‖(Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T + highZeros χ δ x T + R) -
          lowZeros χ δ x T - highZeros χ δ x T - R‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
  have heq :
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x =
      log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) *
          sqrt x + (3 * log q + 14 * |δ| + 17) +
        (log q + 6) * (1 + 6 * |δ|) / sqrt x := by
    generalize hroot : sqrt x = s
    have hxx : x = s ^ 2 := by rw [← hroot, sq_sqrt hx0.le]
    have hsne : s ≠ 0 := by rw [← hroot]; exact hs0.ne'
    rw [hxx]
    field_simp [hsne]
  rw [heq]
  linarith

/-- PROVED from the corrected Lemma 4.1 leaf, Lemma 4.2, and the lab pieces for Lemmas 4.4 and
4.5. P0014 Proposition 4.6, pages 43 and 44, display 4.43 with the recorded factor 6 repair,
written out without Decomp123.gaussianError: the same inequality as
Decomp123.gaussian_explicit_estimate. It does not use the printed Lemma 4.1 leaf. -/
theorem gaussian_explicit_estimate_corrected (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x :=
  assembly_of_components_corrected x hx q χ δ T
    (explicit_formula_remainder_corrected x hx q χ hχ δ T hT hzeros)
    (low_zero_bound_slack x hx q χ hχ δ T hT hzeros)
    (SplitGaussian123.high_zero_bound x hx q χ hχ δ T hT hzeros)

end LeanLab.HelfgottMajor.Lemma41Corrected123

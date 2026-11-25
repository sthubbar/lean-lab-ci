/-
burst-20261122 S124, step feed1122-DecompJ409-p2. P0014 Proposition 4.6, page 43, display 4.43,
for the Gaussian, in the PRINTED form with 1 + 5 abs delta, split along the proof on pages 43
and 44 and the lab route of HelfgottMajor.Lemma41Corrected123.

The printed step |η'|₂ + 2π abs δ |η|₂ ≤ 1 + 5 abs δ of page 44 fails once abs δ is at least 2/5,
HelfgottMajor.Lemma41Terms.printed_fails, and the corrected Lemma 4.1 of the lab carries an extra
log x for even characters. The lab pieces of Lemmas 4.1, 4.4 and 4.5 therefore give display 4.43
with 1 + 6 abs delta only. The printed constant is still reached here: for sqrt x at least
2 (log q + 6) the extra (log q + 6) abs δ x^(-3/2) fits in the slack of the residue budget, and for
smaller x the trivial bound of the sum and of its main term already lies below the x^(-1/2) term
of display 4.43. The only new LEAF is that trivial bound for the sum.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.DecompJ409LeavesProp46
import LeanLab.HelfgottArcs.HeartHat
import LeanLab.HelfgottMajor.Lemma41Corrected123

namespace LeanLab.HelfgottArcs.DecompJ409LeavesProp46S124Prop46
open Real MeasureTheory
open LeanLab.HelfgottArcs LeanLab.HelfgottMajor LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottArcs.DecompJ409LeavesProp46

/-- LEAF: the trivial bound for the twisted Gaussian sum of P0014 display 4.43, by partial
summation from the Chebyshev bound psi of y below 1.03883 y of Rosser and Schoenfeld 1962,
Theorem 12, the bound Helfgott uses for prime sums throughout P0014: the sum is at most
1.03883 sqrt(π/2) x, below 2 x. Class MEDIUM, CITED input. -/
theorem schi_etaHeart_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) (δ x : ℝ) (hx : 1 ≤ x) :
    ‖Schi etaHeart χ δ x‖ ≤ 2 * x := by
  sorry

/-- PROVED. The main term of display 4.43 has norm at most the integral of the one sided
Gaussian, sqrt(2π)/2, by display 4.42 on page 43. -/
theorem fhat_etaHeart_norm_le (t : ℝ) : ‖fhat etaHeart t‖ ≤ 2 := by
  have hnn : ∀ y, 0 ≤ etaHeart y := by
    intro y; unfold etaHeart; split_ifs <;> positivity
  have hnorm : ∀ y : ℝ, ‖e (-(y * t)) * (etaHeart y : ℂ)‖ = etaHeart y := by
    intro y
    have h1 : ‖e (-(y * t))‖ = 1 := by
      simp [e, Complex.norm_exp, Complex.mul_re]
    rw [norm_mul, h1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn y)]
  have hint : ∫ y : ℝ, etaHeart y = sqrt (2 * π) / 2 := by
    have h0 := fhat_etaHeart_zero
    unfold fhat at h0
    have he : ∀ y : ℝ, e (-(y * 0)) = 1 := by intro y; simp [e]
    simp only [he, one_mul] at h0
    rw [integral_complex_ofReal] at h0
    exact_mod_cast h0
  calc ‖fhat etaHeart t‖ ≤ ∫ y : ℝ, ‖e (-(y * t)) * (etaHeart y : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, etaHeart y := by simp_rw [hnorm]
    _ = sqrt (2 * π) / 2 := hint
    _ ≤ 2 := by
      have h : sqrt (2 * π) ≤ 4 := by
        rw [sqrt_le_left (by norm_num)]
        nlinarith [pi_lt_four]
      linarith

/-- PROVED. The arithmetic of page 44 with the corrected inputs, for sqrt x at least
2 (log q + 6): the contour error with 1 + 6 abs δ and the residue budget fit in display 4.43
with 1 + 5 abs δ. -/
theorem large_x_budget {L d s : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d) (hs : 2 * (L + 6) ≤ s) :
    (L + 6.01) * (1 + 6 * d) / s + 13.347 * d + 16.695 ≤
      (L + 6) * (1 + 5 * d) / s + 14 * d + 17 := by
  have hs0 : 0 < s := by linarith
  have key : ((L + 6.01) * (1 + 6 * d) - (L + 6) * (1 + 5 * d)) / s ≤ 0.6 * d + 0.3 := by
    rw [div_le_iff₀ hs0]
    nlinarith [mul_nonneg hd hL, mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 0.6 * d + 0.3)]
  have he : (L + 6.01) * (1 + 6 * d) / s =
      (L + 6) * (1 + 5 * d) / s + ((L + 6.01) * (1 + 6 * d) - (L + 6) * (1 + 5 * d)) / s := by
    ring
  rw [he]
  linarith

/-- The exact parent `prop_4_6` statement from the leaves: the trivial bound leaf above and the
lab pieces of Lemmas 4.1, 4.4 and 4.5 behind Lemma41Corrected123. -/
theorem prop_4_6_of_leaves (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T0 : ℝ) (hT0 : max (4 * π ^ 2 * |δ|) 100 ≤ T0)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T0 → s.re = 1 / 2) :
    MajorShape etaHeart χ δ x (errGauss q T0 δ x) := by
  unfold MajorShape errGauss
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hL : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hT100 : 100 ≤ T0 := (le_max_right _ _).trans hT0
  have hsT : 10 ≤ sqrt T0 := by
    rw [show (10 : ℝ) = sqrt 100 by rw [show (100 : ℝ) = 10 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hT100
  have hlqT : log (q : ℝ) ≤ log (q * T0) := log_le_log (by linarith) (by nlinarith)
  have hHnn : 0 ≤ log (q * T0 / (2 * π)) * (4.329 * exp (-0.1598 * T0) +
      0.802 * |δ| * exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)) := by
    apply mul_nonneg
    · apply log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith [pi_lt_four]
    · positivity
  set A := 2.337 * √T0 * log (q * T0) + 21.817 * √T0 + 2.85 * log q + 74.38 with hA
  have hA8 : 8 * (log q + 6) ≤ A := by
    have : 23.37 * log (q : ℝ) ≤ 2.337 * √T0 * log (q * T0) := by
      nlinarith [mul_le_mul hsT hlqT hL (by linarith)]
    rw [hA]; nlinarith
  have hsq : sqrt x * sqrt x = x := mul_self_sqrt hx0.le
  have heq : (log (q * T0 / (2 * π)) * (4.329 * exp (-0.1598 * T0) +
      0.802 * |δ| * exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)) + A / √x +
      (3 * log q + 14 * |δ| + 17) / x + (log q + 6) * (1 + 5 * |δ|) / (x * √x)) * x =
      log (q * T0 / (2 * π)) * (4.329 * exp (-0.1598 * T0) +
        0.802 * |δ| * exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)) * x + A * √x +
      (3 * log q + 14 * |δ| + 17) + (log q + 6) * (1 + 5 * |δ|) / √x := by
    generalize hroot : sqrt x = s at hsq hs0
    have hsne : s ≠ 0 := hs0.ne'
    rw [← hsq]
    field_simp
  rw [heq]
  have hnn2 : 0 ≤ (3 * log (q : ℝ) + 14 * |δ| + 17) := by positivity
  have hnn3 : 0 ≤ (log (q : ℝ) + 6) * (1 + 5 * |δ|) / √x := by positivity
  by_cases hsmall : sqrt x < 2 * (log q + 6)
  · -- small x: the trivial bound
    have h1 := schi_etaHeart_trivial χ δ x hx
    have h2 : ‖(if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤ 2 * x := by
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
        exact mul_le_mul_of_nonneg_right (fhat_etaHeart_norm_le _) hx0.le
      · simp; linarith
    have h3 := norm_sub_le (Schi etaHeart χ δ x) (if q = 1 then fhat etaHeart (-δ) * x else 0)
    have h4 : 4 * x ≤ A * √x := by
      calc 4 * x = (4 * √x) * √x := by rw [mul_assoc, hsq]
        _ ≤ A * √x := mul_le_mul_of_nonneg_right (by linarith) hs0.le
    have hHx := mul_nonneg hHnn hx0.le
    linarith
  · push_neg at hsmall
    obtain ⟨R, hR, hE⟩ := Lemma41Corrected123.explicit_formula_remainder_corrected x hx q χ hχ δ
      T0 hT0 hzeros
    have hLz := Lemma41Corrected123.low_zero_bound_slack x hx q χ hχ δ T0 hT0 hzeros
    have hHz := SplitGaussian123.high_zero_bound x hx q χ hχ δ T0 hT0 hzeros
    have hlogx : log x ≤ 2 * sqrt x := by
      have h := log_le_sub_one_of_pos hs0
      rw [log_sqrt hx0.le] at h
      linarith
    have htri : ‖Schi etaHeart χ δ x -
        (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
        ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T0 + highZeros χ δ x T0 + R‖ +
          ‖lowZeros χ δ x T0‖ + ‖highZeros χ δ x T0‖ + ‖R‖ := by
      calc
        _ = ‖(Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
            lowZeros χ δ x T0 + highZeros χ δ x T0 + R) -
            lowZeros χ δ x T0 - highZeros χ δ x T0 - R‖ := by congr 1; abel
        _ ≤ _ := (norm_sub_le _ _).trans (by
          gcongr
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
    have hb := large_x_budget hL (abs_nonneg δ) hsmall
    have hLz' : ‖lowZeros χ δ x T0‖ ≤ (A - 2) * sqrt x := by rw [hA]; exact hLz
    nlinarith

end LeanLab.HelfgottArcs.DecompJ409LeavesProp46S124Prop46

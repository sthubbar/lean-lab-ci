import LeanLab.HelfgottMajor.Gaussian123Base

/-!
P0014 Lemma 4.4, pages 39 and 40, display 4.32: the middle mass bound with two units of
proved slack for T at least 100. This is not a printed statement. It is used to pay for the
log x of the corrected Lemma 4.1.
The proof repeats the large height case of Decomp526a.middle_mass_large and keeps the slack
in the final scalar absorption.
CONDITIONAL ON the shared lab count ZeroCount1623.book_zero_count, as
Decomp526a.middle_mass_bound is, and on nothing else. Route burst 2026-11-15, step p6.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MiddleSlack123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open MeasureTheory LeanLab.HelfgottMajor LeanLab.HelfgottMajor.Decomp389b
  LeanLab.HelfgottMajor.Decomp526a Set

/-- PROVED. Scalar absorption of the finite upper endpoint into the page 40 budget of P0014
Lemma 4.4, with two units of slack kept when s is at least 10. Derived arithmetic from the
norms of display 4.42 on page 43, not a printed statement. -/
theorem finite_endpoint_absorption_slack (s L lq : ℝ) (hs : 10 ≤ s) (hL : 0 ≤ L)
    (hlq : 0 ≤ lq) :
    (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog) * s * L +
      11.497 * sqrt Sec45.nLog * s + 2.15581 * (0.3 * lq + 6.778) +
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * (0.15 * L + 3.389) ≤
    (sqrt Sec45.nTwo + sqrt Sec45.nLog) * s * L +
      (17.21 * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * s +
      2.15581 * (0.5 * lq + 17.7) - 2 := by
  have hN0 := sqrt_nonneg Sec45.nTwo
  have hL0 := sqrt_nonneg Sec45.nLog
  have hNlo := Sec45.sqrt_nTwo_gt
  have hNhi := Sec45.sqrt_nTwo_lt
  have hLlo := sqrt_nLog_lower
  have hLhi := Sec45.sqrt_nLog_lt
  have hC := BookP1617.K_bds
  have hprod := mul_le_mul hC.2.le hNhi.le hN0 (by norm_num)
  have hA : (0.9 : ℝ) ≤ sqrt Sec45.nTwo + sqrt Sec45.nLog -
      (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog) := by linarith
  have hB : (4 : ℝ) ≤ 17.21 * sqrt Sec45.nLog -
      log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo - 11.497 * sqrt Sec45.nLog := by
    nlinarith
  have hEL : 3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 0.15 ≤ (1.25 : ℝ) := by
    linarith
  have hEC : 3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 3.389 ≤ (28.1 : ℝ) := by
    linarith
  have hAs := mul_le_mul_of_nonneg_right hA (show 0 ≤ s by linarith)
  have hBs := mul_le_mul_of_nonneg_right hB (show 0 ≤ s by linarith)
  have hAL : 0 ≤ (sqrt Sec45.nTwo + sqrt Sec45.nLog -
      (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog)) * s -
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) * 0.15 := by linarith
  have hp := mul_nonneg hAL hL
  nlinarith

/-- PROVED, CONDITIONAL ON ZeroCount1623.book_zero_count. P0014 Lemma 4.4, pages 39 and 40,
display 4.32: the middle mass bound with two units of slack for T at least 100. Not a printed
statement. -/
theorem middle_mass_bound_slack (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT100 : 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) - 2 := by
  have hT : 2 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have he2 : exp 2 < (8 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos 1]
  have hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T := by
    have hh := mul_le_mul pi_lt_four.le he2.le (exp_pos 2).le (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have hlog : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq
  have hs : (10 : ℝ) ≤ sqrt T := (le_sqrt (by norm_num) hT0.le).mpr (by nlinarith)
  have hW : sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) ≤
      sqrt T * log ((q : ℝ) * T) := by
    apply (Sampling431.main_weight_root_bound (q : ℝ) T hq0 hT1 hlarge).trans
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg T)
    rw [log_div hqT.ne' (by positivity)]
    have hc := BookP1617.K_bds
    linarith
  have hV := Sampling431.error_weight_root_bound (q : ℝ) T hq0 hT1 hlarge
  have hpos := one_sign_finite_sampling q χ δ T 1 hT1 (Or.inl rfl) hzeros
    (fun t ht => signed_count_bound χ hχ 1 t ht)
  have hneg := one_sign_finite_sampling q χ δ T (-1) hT1 (Or.inr rfl) hzeros
    (fun t ht => signed_count_bound χ hχ (-1) t ht)
  have hE := gaussian_line_energy_bound δ
  have hD := gaussian_derivative_energy_bound δ
  have hEp : (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) ≤
      0.565 * sqrt Sec45.nTwo := by
    have hp : 0 < sqrt π := by positivity
    calc
      _ ≤ (2 * sqrt π * sqrt Sec45.nTwo) / (2 * π) :=
        div_le_div_of_nonneg_right hE (by positivity)
      _ = sqrt Sec45.nTwo / sqrt π := by
        rw [show 2 * π = 2 * sqrt π * sqrt π by nlinarith [sq_sqrt pi_pos.le]]
        field_simp
      _ ≤ _ := by
        rw [div_le_iff₀ hp]
        nlinarith [mul_nonneg (sqrt_nonneg Sec45.nTwo)
          (show (0 : ℝ) ≤ 0.565 * sqrt π - 1 by linarith [Sec45.sqrt_pi_gt])]
  have hDp : sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      3.546 * sqrt Sec45.nLog := by
    apply hD.trans
    nlinarith [mul_nonneg (sqrt_nonneg Sec45.nLog)
      (show (0 : ℝ) ≤ 3.546 - 2 * sqrt π by linarith [Sec45.sqrt_pi_lt])]
  have htpos := gaussian_endpoint_trace δ T 1 hT (Or.inl rfl)
  have htneg := gaussian_endpoint_trace δ T (-1) hT (Or.inr rfl)
  have htrace : ‖gaussianMellin δ ((1 / 2 : ℂ) + (1 * T : ℝ) * Complex.I)‖ +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (-1 * T : ℝ) * Complex.I)‖ ≤
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) := by
    have hh := add_le_add htpos htneg
    have hpd : 2 * sqrt π * (sqrt Sec45.nTwo + sqrt Sec45.nLog) ≤
        3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) :=
      mul_le_mul_of_nonneg_right (by linarith [Sec45.sqrt_pi_lt]) (by positivity)
    nlinarith
  have hepos := mellin_critical_norm_le δ ((1 / 2 : ℂ) + (1 : ℂ) * Complex.I) (by norm_num)
  have heneg := mellin_critical_norm_le δ ((1 / 2 : ℂ) + (-1 : ℂ) * Complex.I) (by norm_num)
  have hsample : middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + (1 : ℂ) * Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (-1 : ℂ) * Complex.I)‖) *
        (0.15 * log (q : ℝ) + 3.389) +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + (1 * T : ℝ) * Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (-1 * T : ℝ) * Complex.I)‖) *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
    rw [middle_mass_signed_split]
    norm_num only [Complex.ofReal_one, Complex.ofReal_neg] at hpos hneg
    convert add_le_add hpos hneg using 1 <;> ring
  have hcoarse : middleMass χ δ T ≤
      (0.565 * sqrt Sec45.nTwo + 0.532 * sqrt Sec45.nLog) * sqrt T * log ((q : ℝ) * T) +
      11.497 * sqrt Sec45.nLog * sqrt T + 2.15581 * (0.3 * log (q : ℝ) + 6.778) +
      3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
    calc
      _ ≤ 0.565 * sqrt Sec45.nTwo * (sqrt T * log ((q : ℝ) * T)) +
          (3.546 * sqrt Sec45.nLog) * ((0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T) +
          (2 * 2.15581) * (0.15 * log (q : ℝ) + 3.389) +
          3.546 * (sqrt Sec45.nTwo + sqrt Sec45.nLog) *
            (0.15 * log ((q : ℝ) * T) + 3.389) := by
        apply hsample.trans
        gcongr <;> linarith
      _ ≤ _ := by
        have h1 : 0 ≤ sqrt Sec45.nLog * sqrt T * log ((q : ℝ) * T) := by positivity
        have h2 : 0 ≤ sqrt Sec45.nLog * sqrt T := by positivity
        nlinarith
  have habs := finite_endpoint_absorption_slack (sqrt T) (log ((q : ℝ) * T))
    (log (q : ℝ)) hs hlog hlogq
  linarith

end LeanLab.HelfgottMajor.MiddleSlack123

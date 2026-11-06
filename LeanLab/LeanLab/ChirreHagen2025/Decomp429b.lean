import LeanLab.ChirreHagen2025.Decomp377a

/-!
P0075 pages 4 and 5, displays 2.7 and 2.10.
https://arxiv.org/abs/2512.23534
The pointwise Selberg estimate is separated from its elementary integration.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429b
open MeasureTheory Decomp377a

/-- P0075 page 5 display 2.10, inverse fourth power integral. -/
theorem inverse_fourth_integral (T : ℝ) (hT : 10000 ≤ T) :
    (∫ t in (10000 : ℝ)..T, (t ^ 4)⁻¹) ≤ 1 / (3 * 10 ^ 12) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc 10000 T := by
    rw [Set.uIcc_of_le hT]
    simp
  have h := integral_zpow (a := (10000 : ℝ)) (b := T) (n := (-4 : ℤ))
    (Or.inr ⟨by norm_num, hzero⟩)
  norm_num [zpow_neg, zpow_ofNat] at h
  rw [h]
  have ht0 : 0 < T := by linarith
  have : 0 ≤ (T ^ 3)⁻¹ := by positivity
  linarith

/-- P0075 page 5 display 2.10, elementary integration of the square envelope.
No arithmetic function or zeta function occurs in this component. -/
theorem square_envelope_integral (T : ℝ) (hT : 10000 ≤ T) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 10000 T)
    (hb : ∀ t ∈ Set.Icc (10000 : ℝ) T,
      f t ≤ (522.295 / T) * Real.log t ^ 2 + 20.48 / t ^ 4) :
    (∫ t in (10000 : ℝ)..T, f t) ≤ 522.295 * Real.log T ^ 2 + 7 / 10 ^ 12 := by
  have hT0 : 0 < T := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc 10000 T := by
    rw [Set.uIcc_of_le hT]
    simp
  have hi : IntervalIntegrable (fun t : ℝ => (t ^ 4)⁻¹) volume 10000 T := by
    simpa only [zpow_neg, zpow_ofNat] using
      (intervalIntegral.intervalIntegrable_zpow (μ := volume) (a := (10000 : ℝ)) (b := T)
        (n := (-4 : ℤ)) (Or.inr hzero))
  have hg := (intervalIntegrable_const (c := (522.295 / T) * Real.log T ^ 2)
    (a := (10000 : ℝ)) (b := T) (μ := volume)).add (hi.const_mul 20.48)
  calc
    _ ≤ ∫ t in (10000 : ℝ)..T,
        ((522.295 / T) * Real.log T ^ 2 + 20.48 * (t ^ 4)⁻¹) := by
      apply intervalIntegral.integral_mono_on hT hf hg
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
      have hlog := Real.log_le_log ht0 ht.2
      have hsq := pow_le_pow_left₀ hl0 hlog 2
      have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 522.295 / T by positivity)
      exact (hb t ht).trans (add_le_add hmul (by rw [div_eq_mul_inv]))
    _ = (T - 10000) * ((522.295 / T) * Real.log T ^ 2) +
        20.48 * (∫ t in (10000 : ℝ)..T, (t ^ 4)⁻¹) := by
      rw [intervalIntegral.integral_add (intervalIntegrable_const) (hi.const_mul _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
    _ ≤ 522.295 * Real.log T ^ 2 + 7 / 10 ^ 12 := by
      have hfirst : (T - 10000) * ((522.295 / T) * Real.log T ^ 2) ≤
          522.295 * Real.log T ^ 2 := by
        calc
          _ ≤ T * ((522.295 / T) * Real.log T ^ 2) := by
            gcongr
            linarith
          _ = _ := by field_simp
      have hlast := mul_le_mul_of_nonneg_left (inverse_fourth_integral T hT)
        (show (0 : ℝ) ≤ 20.48 by norm_num)
      linarith

/-- P0075 pages 4 and 5, continuity supplies actual error-square integrability. -/
theorem remainder_square_integrable (T : ℝ) (hT : 10000 ≤ T) :
    IntervalIntegrable (fun t : ℝ =>
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ^ 2) volume 10000 T := by
  apply ContinuousOn.intervalIntegrable_of_Icc hT
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hs : (1 : ℂ) + t * Complex.I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact ht0 hi
  have harg : ContinuousAt (fun x : ℝ => (1 : ℂ) + x * Complex.I) t := by fun_prop
  have hz : ContinuousAt (fun x : ℝ => riemannZeta (1 + x * Complex.I)) t :=
    ContinuousAt.comp (g := riemannZeta) (f := fun x : ℝ => (1 : ℂ) + x * Complex.I)
      (differentiableAt_riemannZeta hs).continuousAt harg
  have hd : ContinuousAt (fun x : ℝ => deriv riemannZeta (1 + x * Complex.I)) t :=
    ContinuousAt.comp (g := deriv riemannZeta) (f := fun x : ℝ => (1 : ℂ) + x * Complex.I)
      (analyticOn_riemannZeta.deriv.continuousOn.continuousAt
        (isOpen_compl_singleton.mem_nhds hs)) harg
  have hn : riemannZeta ((1 : ℂ) + t * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  exact (((hd.div hz hn).add (polynomial_continuous T).continuousAt).norm.pow 2).continuousWithinAt

/-- P0075 page 5, numerical coefficient with lambda equal to 1.278. -/
theorem selberg_coefficient_bound :
    40.5 * ((1 + Real.exp 1.278) / 1.278) ^ 2 ≤ 522.295 := by
  have he : Real.exp (0.278 : ℝ) ≤ (∑ m ∈ Finset.range 10,
      (0.278 : ℝ) ^ m / m.factorial) +
      (0.278 : ℝ) ^ 10 * (10 + 1) / ((10 : ℕ).factorial * 10) :=
    Real.exp_bound' (by norm_num) (by norm_num) (by norm_num : 0 < (10 : ℕ))
  norm_num [Finset.sum_range_succ] at he
  have hexp : Real.exp (1.278 : ℝ) ≤ 3.589454 := by
    rw [show (1.278 : ℝ) = 1 + 0.278 by norm_num, Real.exp_add]
    have hmul := mul_le_mul Real.exp_one_lt_d9.le he (Real.exp_pos _).le
      (by norm_num : (0 : ℝ) ≤ 2.7182818286)
    norm_num at hmul
    linarith
  calc
    _ ≤ 40.5 * ((1 + (3.589454 : ℝ)) / 1.278) ^ 2 := by
      gcongr
    _ ≤ 522.295 := by norm_num

/-- LEAF. P0075 page 4 display 2.7 and the bound immediately below it.
The Selberg formula with lambda equal to 1.278 and xy equal to T gives
this pointwise norm envelope. Its zero kernel uses Lemma 2.2 part 2.
The elementary terms are 0.3 and 2.9 over t squared. No mean-square
integration or decimal coefficient rounding is asserted by this leaf. -/
theorem selberg_pointwise_remainder (hRH : RiemannHypothesis) (T : ℝ)
    (hT : 4 * 10 ^ 13 ≤ T) (t : ℝ) (ht : t ∈ Set.Icc (10000 : ℝ) T) :
    ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ≤
      (9 * (1 + Real.exp 1.278) / (2 * 1.278 * Real.sqrt T)) * Real.log t +
        3.2 / t ^ 2 := by
  sorry

/-- P0075 page 5 display 2.10, the square envelope from the norm envelope.
CONDITIONAL ON the smaller pointwise Selberg formula estimate. -/
theorem selberg_square_envelope (hRH : RiemannHypothesis) (T : ℝ)
    (hT : 4 * 10 ^ 13 ≤ T) (t : ℝ) (ht : t ∈ Set.Icc (10000 : ℝ) T) :
    ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ^ 2 ≤
      (522.295 / T) * Real.log t ^ 2 + 20.48 / t ^ 4 := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  let C := 9 * (1 + Real.exp 1.278) / (2 * 1.278 * Real.sqrt T)
  have hc : 2 * C ^ 2 ≤ 522.295 / T := by
    have heq : 2 * C ^ 2 =
        (40.5 * ((1 + Real.exp 1.278) / 1.278) ^ 2) / T := by
      dsimp [C]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hT0.le]
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right selberg_coefficient_bound hT0.le
  have hnorm := pow_le_pow_left₀
    (norm_nonneg (deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) + polynomial T t))
    (selberg_pointwise_remainder hRH T hT t ht) 2
  have hcross := sq_nonneg (C * Real.log t - 3.2 / t ^ 2)
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log t))
  have heq : 2 * (3.2 / t ^ 2) ^ 2 = 20.48 / t ^ 4 := by
    rw [div_pow]
    ring
  change _ ≤ (522.295 / T) * Real.log t ^ 2 + _
  dsimp only [C] at hcross hmul ⊢
  nlinarith

/-- Exact existing Decomp377a.remainder_mean_square statement.
CONDITIONAL ON the smaller pointwise Selberg square envelope. -/
theorem remainder_mean_square (hRH : RiemannHypothesis) (T : ℝ)
    (hT : 4 * 10 ^ 13 ≤ T) :
    IntervalIntegrable (fun t : ℝ =>
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ^ 2) volume (10 ^ 4) T ∧
    (∫ t in (10 ^ 4 : ℝ)..T,
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I) +
        polynomial T t‖ ^ 2) ≤
      522.295 * Real.log T ^ 2 + 7 / 10 ^ 12 := by
  have hT' : 10000 ≤ T := by linarith
  norm_num only [show (10 : ℝ) ^ 4 = 10000 by norm_num]
  refine ⟨remainder_square_integrable T hT', ?_⟩
  convert square_envelope_integral T hT' _ (remainder_square_integrable T hT')
    (selberg_square_envelope hRH T hT) using 1 <;> norm_num

end LeanLab.ChirreHagen2025.Decomp429b

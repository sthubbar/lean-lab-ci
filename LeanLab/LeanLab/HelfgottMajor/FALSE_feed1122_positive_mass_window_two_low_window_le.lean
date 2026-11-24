import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le

/-!
Refutation of the two window leaves `positive_mass_window_two_low_window_le` and
`positive_mass_window_two_high_window_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le`, burst 20261122 S93, and of the
statement they were cut from, `positive_mass_window_two_le` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral`, together with the two half leaves
of `SPLIT_positive_mass_window_two_low_window_le`.

Each of these statements bounds a sum of norms, which is never negative, by a positive multiple
of the mean weight integral `(1 / (2 * pi)) * integral over [1, T] of the critical line norm of the
Gaussian Mellin transform times log (q * t / (2 * pi))`, with no hypothesis tying `q * T` to
`2 * pi`. Take `q = 1`, the trivial character, `delta = 0` and `T = 5 / 4`. Every zero counted has
ordinate at most `5 / 4`, below every band from three halves up, so the left side is zero. On
`[1, 5 / 4]` the weight `log (t / (2 * pi))` is negative and the Gaussian Mellin transform at
`delta = 0` equals `2 ^ (s / 2 - 1) * Gamma (s / 2)`, which never vanishes for `re s > 0`. So the
right side is strictly negative and every one of these statements fails. The same counterexample
was found for the sister band `(5 / 4, 3 / 2]` on branch
`claude/HelfgottMajor-feed1122-SPLIT_positive_mass_window_one_le`; the helper lemmas below are a
copy of the ones proved there, since that branch is not on main. The missing input is the
hypothesis `2 * pi * exp 2 ≤ q * T` carried by the statement this band descends from.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122W3WindowTwoFalse
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.Decomp269a LeanLab.HelfgottMajor.Decomp269b
  LeanLab.HelfgottMajor.Decomp389b LeanLab.HelfgottMajor.Decomp431a

/-- Closed form of the Gaussian Mellin transform at `delta = 0`, valid for `re s > 0`. -/
theorem gaussianMellin_zero_eq (s : ℂ) (hs : 0 < s.re) :
    gaussianMellin 0 s =
      ((|(2 : ℝ)|⁻¹ : ℝ) : ℂ) * ((((1 / 2 : ℝ) : ℂ) ^ (-(s / 2))) * Complex.Gamma (s / 2)) := by
  have hre : 0 < (s / 2).re := by simp; linarith
  have h2 := mellin_comp_mul_left (fun x : ℝ => ((exp (-x) : ℝ) : ℂ)) (s / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hG : Complex.Gamma (s / 2) = mellin (fun x : ℝ => ((exp (-x) : ℝ) : ℂ)) (s / 2) := by
    rw [Complex.Gamma_eq_integral hre, Complex.GammaIntegral_eq_mellin]
  calc gaussianMellin 0 s
      = mellin (fun t : ℝ => (fun u : ℝ => ((exp (-((1 / 2 : ℝ) * u)) : ℝ) : ℂ))
          (t ^ (2 : ℝ))) s := by
        unfold gaussianMellin
        congr 1
        funext t
        simp only [e, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
          Real.rpow_two]
        congr 2
        ring
    _ = (|(2 : ℝ)|⁻¹ : ℝ) • mellin (fun u : ℝ => ((exp (-((1 / 2 : ℝ) * u)) : ℝ) : ℂ))
          (s / ((2 : ℝ) : ℂ)) :=
          mellin_comp_rpow (fun u : ℝ => ((exp (-((1 / 2 : ℝ) * u)) : ℝ) : ℂ)) s 2
    _ = _ := by
        rw [show ((2 : ℝ) : ℂ) = 2 by norm_num, h2, ← hG, Complex.real_smul, smul_eq_mul]

theorem gaussianMellin_zero_ne (s : ℂ) (hs : 0 < s.re) : gaussianMellin 0 s ≠ 0 := by
  have hre : 0 < (s / 2).re := by simp; linarith
  rw [gaussianMellin_zero_eq s hs]
  refine mul_ne_zero (by norm_num) (mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hre))
  rw [Ne, Complex.cpow_eq_zero_iff]
  intro h
  norm_num at h

theorem gaussianMellin_zero_line_continuous :
    Continuous (fun t : ℝ => gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)) := by
  have hre : ∀ t : ℝ, 0 < ((1 / 2 : ℂ) + (t : ℝ) * Complex.I).re := by
    intro t; simp
  have heq : (fun t : ℝ => gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)) =
      fun t : ℝ => ((|(2 : ℝ)|⁻¹ : ℝ) : ℂ) * ((((1 / 2 : ℝ) : ℂ) ^
        (-(((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2))) *
          Complex.Gamma (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2)) := by
    funext t; exact gaussianMellin_zero_eq _ (hre t)
  rw [heq]
  have hlin : Continuous (fun t : ℝ => ((1 / 2 : ℂ) + (t : ℝ) * Complex.I) / 2) := by
    fun_prop
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · exact Continuous.const_cpow hlin.neg (Or.inl (by norm_num))
  · rw [continuous_iff_continuousAt]
    intro t
    refine (Complex.differentiableAt_Gamma _ ?_).continuousAt.comp hlin.continuousAt
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- For the trivial character modulo one, `delta = 0` and `1 < T <= 5 / 4`, the mean weight
integral is strictly negative, since the log weight is negative below `2 * pi` and the Gaussian
Mellin norm is positive and continuous on the critical line. -/
theorem mean_weight_integral_neg (T : ℝ) (hT1 : 1 < T) (hT2 : T ≤ 5 / 4) :
    (∫ t in (1 : ℝ)..T, ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        log (((1 : ℕ) : ℝ) * t / (2 * π))) < 0 := by
  have hpi : (5 / 4 : ℝ) < 2 * π := by linarith [pi_gt_three]
  have hneg : 0 < ∫ t in (1 : ℝ)..T,
      -(‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        log (((1 : ℕ) : ℝ) * t / (2 * π))) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ hT1
    · refine (ContinuousOn.intervalIntegrable ?_).neg
      refine ContinuousOn.mul gaussianMellin_zero_line_continuous.norm.continuousOn ?_
      refine ContinuousOn.log (by fun_prop) ?_
      intro t ht
      rw [Set.uIcc_of_le hT1.le] at ht
      have : 0 < t := by linarith [ht.1]
      positivity
    · intro t ht
      have hn : 0 < ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ :=
        norm_pos_iff.mpr (gaussianMellin_zero_ne _ (by simp))
      have hlog : log (((1 : ℕ) : ℝ) * t / (2 * π)) < 0 := by
        apply Real.log_neg
        · have : 0 < t := by linarith [ht.1]
          positivity
        · rw [Nat.cast_one, one_mul, div_lt_one (by positivity)]
          linarith [ht.2]
      nlinarith
  rw [intervalIntegral.integral_neg] at hneg
  linarith

/-- A band sum is zero when the band lies above the height cap of the zero family. -/
theorem band_sum_eq_zero (T a b : ℝ) (hTa : T ≤ a) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | a < ρ.val.im ∧ ρ.val.im ≤ b}
          (fun ρ => ‖mellinMassTerm (1 : DirichletCharacter ℂ 1) 0 ρ.val‖) ρ) = 0 := by
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  rw [Set.indicator_of_notMem]
  intro hρ
  have h1 := ρ.2.2.2.2
  have h2 := ((le_abs_self ρ.val.im).trans h1).trans hTa
  exact absurd hρ.1 (not_lt.mpr h2)

/-- The general shape of the counterexample: any band starting at or above `5 / 4`, charged any
positive multiple of the mean weight integral, fails at `q = 1`, `delta = 0`, `T = 5 / 4`. -/
theorem FALSE_band_bound (a b c : ℝ) (ha : 5 / 4 ≤ a) (hc : 0 < c) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | a < ρ.val.im ∧ ρ.val.im ≤ b}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      c * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) := by
  intro H
  have h := H 1 (1 : DirichletCharacter ℂ 1) 0 (5 / 4) (by norm_num)
  rw [band_sum_eq_zero (5 / 4) a b ha] at h
  have hI := mean_weight_integral_neg (5 / 4) (by norm_num) le_rfl
  have hp : 0 < 1 / (2 * π) := by positivity
  have hm : 0 < (1 / (2 * π)) * (-(∫ t in (1 : ℝ)..(5 / 4 : ℝ),
      ‖gaussianMellin 0 ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
        log (((1 : ℕ) : ℝ) * t / (2 * π)))) := mul_pos hp (by linarith)
  have := mul_pos hc hm
  nlinarith

/-- The negation of `positive_mass_window_two_low_window_le`. -/
theorem FALSE_positive_mass_window_two_low_window_le :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) :=
  FALSE_band_bound (3 / 2) (7 / 4) (1 / 4) (by norm_num) (by norm_num)

/-- The negation of `positive_mass_window_two_high_window_le`. -/
theorem FALSE_positive_mass_window_two_high_window_le :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 7 / 4 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 4) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) :=
  FALSE_band_bound (7 / 4) 2 (1 / 4) (by norm_num) (by norm_num)

/-- The negation of the parent `positive_mass_window_two_le`. -/
theorem FALSE_positive_mass_window_two_le :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 2}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 2) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) :=
  FALSE_band_bound (3 / 2) 2 (1 / 2) (by norm_num) (by norm_num)

/-- The negation of the deeper leaf `positive_mass_window_two_low_window_low_half_le`. -/
theorem FALSE_positive_mass_window_two_low_window_low_half_le :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 3 / 2 < ρ.val.im ∧ ρ.val.im ≤ 13 / 8}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) :=
  FALSE_band_bound (3 / 2) (13 / 8) (1 / 8) (by norm_num) (by norm_num)

/-- The negation of the deeper leaf `positive_mass_window_two_low_window_high_half_le`. -/
theorem FALSE_positive_mass_window_two_low_window_high_half_le :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ), 1 ≤ T →
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 13 / 8 < ρ.val.im ∧ ρ.val.im ≤ 7 / 4}
          (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / 8) * ((1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))))) :=
  FALSE_band_bound (13 / 8) (7 / 4) (1 / 8) (by norm_num) (by norm_num)


end LeanLab.HelfgottMajor.Feed1122W3WindowTwoFalse

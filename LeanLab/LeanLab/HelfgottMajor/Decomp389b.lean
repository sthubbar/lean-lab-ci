import LeanLab.HelfgottMajor.Decomp389c

/-!
A supply decomposition of Decomp269b.middle_mass_bound.
Source P0014 book Part IV, pages 433 and 434, Lemma 16.10 and display 16.26.
The book treats positive and negative imaginary parts separately.
The old sealed file stays unchanged. The small qT branch is in Decomp389c.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp389b
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The positive parameter half line energy on the critical line, book page 434.
The sign parameter is used only at 1 and minus 1 in the sampling proof.
-/
noncomputable def lineEnergy (δ ε : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2

/-- The derivative energy above height 1 on either sign of the line, book page 434. -/
noncomputable def derivativeEnergy (δ ε : ℝ) : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ),
    ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I)‖ ^ 2

/-- LEAF. Book pages 433 and 434, display 16.26 and the following g squared estimate.
This is the zero sampling reduction before either Mellin energy is evaluated.
It uses the two signs separately and keeps both endpoint norms explicit.
-/
theorem middle_sampling_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
        (0.15 * log (q : ℝ) + 3.389) := by
  sorry

/-- LEAF. Book page 434, the first Plancherel estimate after display 16.26.
The Gaussian square moment is display 4.42 on P0014 page 43.
This has no character, zero count or height parameter.
-/
theorem gaussian_line_energy_bound (δ : ℝ) :
    sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo := by
  sorry

/-- LEAF. Book page 434, the differentiated Mellin Plancherel estimate.
The Gaussian log squared moment is display 4.42 on P0014 page 43.
This has no character, zero count or height parameter.
-/
theorem gaussian_derivative_energy_bound (δ : ℝ) :
    sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog := by
  sorry

/-- The book coefficients of Lemma 16.10 are below the older page 40 coefficients.
Only arithmetic is asserted. No zero sampling input is used.
-/
theorem book_coefficients_le :
    sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog ≤
      sqrt Sec45.nTwo + sqrt Sec45.nLog ∧
    6.484 * sqrt π * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo ≤
      17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := by
  have hs1 : (1 : ℝ) ≤ sqrt π := by linarith [Sec45.sqrt_pi_gt]
  have hs2 : sqrt π ≤ (2 : ℝ) := by linarith [Sec45.sqrt_pi_lt]
  have hs0 : 0 < sqrt π := by positivity
  have hN0 := sqrt_nonneg Sec45.nTwo
  have hL0 := sqrt_nonneg Sec45.nLog
  obtain ⟨hC0, hC⟩ := BookP1617.K_bds
  have hCpos : 0 ≤ log (2 * π * sqrt (exp 1)) := by linarith
  have hprod0 : 0 ≤ log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo := mul_nonneg hCpos hN0
  have hLge : (0.8 : ℝ) ≤ sqrt Sec45.nLog := by
    have hh := Decomp389c.middle_constant_ge
    linarith
  have hprod : log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo ≤ 2.3378771 * 0.941397 :=
    mul_le_mul hC.le Sec45.sqrt_nTwo_lt.le hN0 (by norm_num)
  constructor
  · have hdiv : sqrt Sec45.nTwo / sqrt π ≤ sqrt Sec45.nTwo := by
      rw [div_le_iff₀ hs0]
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hs1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs2) hL0]
  · have hnonneg : 0 ≤ log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hs2) hL0]

/-- The large qT branch follows from independent sampling and energy inputs.
CONDITIONAL ON those explicit inputs. Book pages 433 and 434.
-/
theorem large_middle_bound_of_inputs (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hsampling : middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
        (0.15 * log (q : ℝ) + 3.389))
    (henergy : sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo)
    (hderiv : sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nLog) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT0 : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have hsπ : 0 < sqrt π := by positivity
  have hsT := sqrt_nonneg T
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq
  have hlog : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hC : 0 < 2 * π * sqrt (exp 1) := by positivity
  have he : sqrt (exp 1) ≤ exp 2 := by
    have hs : sqrt (exp 1) ≤ 2 := (sqrt_le_iff).mpr ⟨by norm_num, by linarith [exp_one_lt_three]⟩
    have hh : (2 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
    exact hs.trans hh
  have hshift : 0 ≤ log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) := by
    apply log_nonneg
    rw [le_div_iff₀ hC]
    have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * π)
    nlinarith
  have hE : (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) ≤
      sqrt Sec45.nTwo / sqrt π := by
    calc
      _ ≤ (2 * sqrt π * sqrt Sec45.nTwo) / (2 * π) :=
        div_le_div_of_nonneg_right henergy (by positivity)
      _ = _ := by
        rw [show 2 * π = 2 * sqrt π * sqrt π by nlinarith [sq_sqrt pi_pos.le]]
        field_simp
  have hp := Decomp389a.mellin_critical_norm_le δ ((1 / 2 : ℂ) + Complex.I)
    (by norm_num) HalfMoment389.gaussian_half_moment_bound
  have hn := Decomp389a.mellin_critical_norm_le δ ((1 / 2 : ℂ) - Complex.I)
    (by norm_num) HalfMoment389.gaussian_half_moment_bound
  have hmain : middleMass χ δ T ≤
      (sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog) * sqrt T * log ((q : ℝ) * T) +
      (6.484 * sqrt π * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.3 * log (q : ℝ) + 6.778) := by
    calc
      _ ≤ sqrt Sec45.nTwo / sqrt π * sqrt T *
          log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
          (2 * sqrt π * sqrt Sec45.nLog) * (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
          (2 * 2.15581) * (0.15 * log (q : ℝ) + 3.389) := by
        apply hsampling.trans
        gcongr <;> linarith
      _ = _ := by
        rw [log_div hqT0.ne' hC.ne']
        ring
  obtain ⟨hA, hB⟩ := book_coefficients_le
  have ha := mul_le_mul_of_nonneg_right hA (mul_nonneg hsT hlog)
  have hb := mul_le_mul_of_nonneg_right hB hsT
  nlinarith

/-- Exactly Decomp269b.middle_mass_bound, from sampling, two energies and the small count branch.
This assembly has no sorry of its own and invokes no old sorry theorem.
-/
theorem middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  by_cases hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T
  · exact large_middle_bound_of_inputs q χ δ T hT hlarge
      (middle_sampling_bound q χ hχ δ T hT hlarge hzeros)
      (gaussian_line_energy_bound δ) (gaussian_derivative_energy_bound δ)
  · exact Decomp389c.small_middle_mass_bound q χ hχ δ T hT (le_of_not_ge hlarge) hzeros

end LeanLab.HelfgottMajor.Decomp389b

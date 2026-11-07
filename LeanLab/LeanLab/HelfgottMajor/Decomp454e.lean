import LeanLab.HelfgottMajor.Gaussian309
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
A coarse unshifted Mellin decay bound for the convergence half of Lemma 4.5.
Source P0014 page 29, the Gaussian Gamma formula, and page 41 display 4.33.
The polynomial bound does not give the sharp exponential tail budget.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp454e
open Real MeasureTheory Set
open LeanLab.HelfgottArcs Decomp269a

/-- Euler's integral bounds the complex Gamma norm by Gamma of the real part.
Derived prerequisite for the unshifted formula discussed on P0014 page 29.
-/
theorem norm_Gamma_le_real (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  calc ‖∫ t in Ioi (0 : ℝ), (exp (-t) : ℂ) * (t : ℂ) ^ (s - 1)‖
      ≤ ∫ t in Ioi (0 : ℝ), ‖(exp (-t) : ℂ) * (t : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0 : ℝ), exp (-t) * t ^ (s.re - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [norm_mul, Complex.norm_of_nonneg (exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos ht]
      simp

/-- A fixed Gamma bound on the shifted strip used in the unshifted tail estimate.
Derived from Euler's integral and Gamma monotonicity, for P0014 page 41 display 4.33.
-/
theorem norm_Gamma_shift_four_le (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    ‖Complex.Gamma (s / 2 + 4)‖ ≤ 24 := by
  have hr : (s / 2 + 4).re = s.re / 2 + 4 := by simp
  have hpos : 0 < (s / 2 + 4).re := by rw [hr]; linarith
  have hg : Real.Gamma ((s / 2 + 4).re) ≤ Real.Gamma 5 := by
    apply Real.Gamma_strictMonoOn_Ici.monotoneOn
    · rw [mem_Ici, hr]
      linarith
    · norm_num
    · rw [hr]
      linarith
  have h5 : Real.Gamma 5 = 24 := by
    norm_num [Real.Gamma_nat_eq_factorial]
  exact (norm_Gamma_le_real _ hpos).trans (h5 ▸ hg)

/-- Four Gamma recurrences regularize four powers of the high ordinate.
Derived from the unshifted Mellin formula before display 3.76 on P0014 page 29.
-/
theorem mellin_zero_shift_four (s : ℂ) (hs : 0 < s.re) :
    (s / 2 * (s / 2 + 1) * (s / 2 + 2) * (s / 2 + 3)) * gaussianMellin 0 s =
      (1 / 2 : ℂ) * (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2 + 4) := by
  have hn (k : ℕ) : s / 2 + (k : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, Complex.zero_re] at hr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h0 : Complex.Gamma (s / 2 + 1) = s / 2 * Complex.Gamma (s / 2) := by
    simpa using Complex.Gamma_add_one (s / 2) (by simpa using hn 0)
  have h1 : Complex.Gamma (s / 2 + 2) =
      (s / 2 + 1) * Complex.Gamma (s / 2 + 1) := by
    simpa only [add_assoc, one_add_one_eq_two] using
      Complex.Gamma_add_one (s / 2 + 1) (by simpa using hn 1)
  have h2 : Complex.Gamma (s / 2 + 3) =
      (s / 2 + 2) * Complex.Gamma (s / 2 + 2) := by
    simpa only [add_assoc, show (2 : ℂ) + 1 = 3 by norm_num] using
      Complex.Gamma_add_one (s / 2 + 2) (by simpa using hn 2)
  have h3 : Complex.Gamma (s / 2 + 4) =
      (s / 2 + 3) * Complex.Gamma (s / 2 + 3) := by
    simpa only [add_assoc, show (3 : ℂ) + 1 = 4 by norm_num] using
      Complex.Gamma_add_one (s / 2 + 3) (by simpa using hn 3)
  rw [Gaussian309.mellin_zero_shift s hs, h3, h2, h1, h0]
  ring

/-- A uniform fourth power decay bound in the unshifted open critical strip.
This is a coarse convergence supply for P0014 page 41 display 4.33.
It does not imply the exponential numerical bound of Lemma 4.5.
-/
theorem mellin_zero_shift_polynomial_decay (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    ‖gaussianMellin 0 s‖ * |s.im| ^ 4 ≤ 384 := by
  have hlow (k : ℕ) : |s.im| / 2 ≤ ‖s / 2 + (k : ℂ)‖ := by
    have hh := Complex.abs_im_le_norm (s / 2 + (k : ℂ))
    simpa only [Complex.add_im, Complex.div_ofNat_im, Complex.natCast_im, add_zero,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hh
  have hpow : ‖(2 : ℂ) ^ (s / 2)‖ ≤ 2 := by
    have hh : ‖(2 : ℂ) ^ (s / 2)‖ = (2 : ℝ) ^ (s.re / 2) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (s / 2)
    rw [hh]
    calc (2 : ℝ) ^ (s.re / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  have hupper : ‖(1 / 2 : ℂ) * (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2 + 4)‖ ≤ 24 := by
    rw [norm_mul, norm_mul]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    have hg := norm_Gamma_shift_four_le s hs hs1
    nlinarith [mul_le_mul hpow hg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  have h01 := mul_le_mul (hlow 0) (hlow 1) (by positivity : (0 : ℝ) ≤ |s.im| / 2)
    (norm_nonneg (s / 2 + (0 : ℕ)))
  have h23 := mul_le_mul (hlow 2) (hlow 3) (by positivity : (0 : ℝ) ≤ |s.im| / 2)
    (norm_nonneg (s / 2 + (2 : ℕ)))
  have hprod := mul_le_mul h01 h23 (by positivity) (by positivity)
  norm_num only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at hprod
  have hnorm := congrArg norm (mellin_zero_shift_four s hs)
  simp only [norm_mul] at hnorm
  simp only [norm_mul] at hupper
  have hm := mul_le_mul_of_nonneg_right hprod (norm_nonneg (gaussianMellin 0 s))
  nlinarith [hupper, hnorm, hm]

end LeanLab.HelfgottMajor.Decomp454e

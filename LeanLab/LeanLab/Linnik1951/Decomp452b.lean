/-
Original page 157 Gamma asymptotic preceding equation 4.4.
A lower estimate is useful when checking the absolute kernel split.
The reflection formula and the existing strip upper bound suffice.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.PNTPort.ZetaZeros.GammaBounds

namespace LeanLab.Linnik1951
open scoped ComplexConjugate

/-- The sine factor in the reflection formula grows at most exponentially. -/
theorem norm_sin_le_exp_im452 (z : ℂ) (hz : 0 ≤ z.im) :
    ‖Complex.sin z‖ ≤ Real.exp z.im := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have h := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  have h1 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [h1, h2] at h
  have he : Real.exp (-z.im) ≤ Real.exp z.im := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- On the reflected strip, shifting Gamma once removes the polynomial loss. -/
theorem reflected_gamma_upper452 (s : ℂ) (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (ht : 1 ≤ s.im) :
    ‖Complex.Gamma (1 - s)‖ ≤
      3 * Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * s.im / 2)) := by
  have hne : (1 - s : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hn : 1 ≤ ‖(1 - s : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (1 - s)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg,
      abs_of_nonneg (by linarith : 0 ≤ s.im)] at h
    linarith
  have hshift : Complex.Gamma (2 - s) = (1 - s) * Complex.Gamma (1 - s) := by
    rw [show (2 - s : ℂ) = (1 - s) + 1 by ring]
    exact Complex.Gamma_add_one (1 - s) hne
  have hg := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL
    (s := star (2 - s)) (by simp; linarith) (by simp; linarith)
  have hnorm : ‖star (2 - s : ℂ) + 1‖ = ‖(2 - s : ℂ) + 1‖ := by
    simpa using norm_star ((2 - s : ℂ) + 1)
  have hgnorm : ‖Complex.Gamma (star (2 - s : ℂ))‖ = ‖Complex.Gamma (2 - s)‖ := by
    simp only [Complex.star_def, Complex.Gamma_conj, Complex.norm_conj]
  have him : (star (2 - s : ℂ)).im = s.im := by simp
  rw [hgnorm, hnorm, him, hshift, norm_mul] at hg
  have hp : ‖(2 - s : ℂ) + 1‖ ≤ 3 * ‖(1 - s : ℂ)‖ := by
    have heq : (2 - s : ℂ) + 1 = (1 - s) + 2 := by ring
    rw [heq]
    have h := norm_add_le (1 - s : ℂ) 2
    norm_num at h
    linarith
  have hg' := hg.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) (Real.exp_pos _).le)
  nlinarith [norm_pos_iff.mpr hne]

/-- A lower Gamma estimate on the Mellin strip for positive frequencies. -/
theorem gamma_lower452 (s : ℂ) (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (ht : 1 ≤ s.im) :
    Real.pi / (3 * Real.sqrt (2 * Real.pi)) * Real.exp (-(Real.pi * s.im / 2)) ≤
      ‖Complex.Gamma s‖ := by
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    apply Complex.sin_ne_zero_iff.mpr
    intro k hk
    have hi := congrArg Complex.im hk
    simp at hi
    have : 0 < Real.pi * s.im := mul_pos Real.pi_pos (by linarith)
    linarith
  have href := congrArg norm (Complex.Gamma_mul_Gamma_one_sub s)
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at href
  have hprod : Real.pi = ‖Complex.Gamma s‖ * ‖Complex.Gamma (1 - s)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * s)‖ := by
    exact ((eq_div_iff (norm_ne_zero_iff.mpr hsin)).mp href).symm
  have hsine := norm_sin_le_exp_im452 ((Real.pi : ℂ) * s) (by simp; positivity)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hsine
  have hgamma := reflected_gamma_upper452 s hlo hhi ht
  have hbound : Real.pi ≤ ‖Complex.Gamma s‖ *
      (3 * Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * s.im / 2))) *
      Real.exp (Real.pi * s.im) := by
    calc Real.pi = _ := hprod
         _ ≤ _ := mul_le_mul
           (mul_le_mul_of_nonneg_left hgamma (norm_nonneg (Complex.Gamma s)))
           hsine (norm_nonneg _) (by positivity)
  have he : Real.exp (-(Real.pi * s.im / 2)) * Real.exp (Real.pi * s.im) =
      Real.exp (Real.pi * s.im / 2) := by rw [← Real.exp_add]; congr 1; ring
  have hbound' : Real.pi ≤ ‖Complex.Gamma s‖ *
      (3 * Real.sqrt (2 * Real.pi)) * Real.exp (Real.pi * s.im / 2) := by
    have heq : ‖Complex.Gamma s‖ *
        (3 * Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * s.im / 2))) *
        Real.exp (Real.pi * s.im) = ‖Complex.Gamma s‖ *
        (3 * Real.sqrt (2 * Real.pi)) * Real.exp (Real.pi * s.im / 2) := by
      calc _ = ‖Complex.Gamma s‖ * (3 * Real.sqrt (2 * Real.pi)) *
          (Real.exp (-(Real.pi * s.im / 2)) * Real.exp (Real.pi * s.im)) := by ring
           _ = _ := by rw [he]
    rwa [heq] at hbound
  have hc : 0 < 3 * Real.sqrt (2 * Real.pi) := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, div_div, div_le_iff₀ (mul_pos hc (Real.exp_pos _))]
  nlinarith [hbound']

/-- A small angular gap prevents the absolute Mellin kernel from decaying. -/
theorem kernel_lower_of_gap452 (s z : ℂ) (K : ℝ)
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1) (ht : 1 ≤ s.im)
    (hz1 : 1 ≤ ‖z‖) (hzK : ‖z‖ ≤ K)
    (hgap : (Real.pi / 2 - z.arg) * s.im ≤ 1) :
    Real.pi / (3 * Real.sqrt (2 * Real.pi)) / K * Real.exp (-1) ≤
      ‖z ^ (-s) * Complex.Gamma s‖ := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hK : 0 < K := lt_of_lt_of_le hzpos hzK
  have hz : z ≠ 0 := norm_ne_zero_iff.mp hzpos.ne'
  have hpow : 1 / K ≤ ‖z‖ ^ (-s.re) := by
    calc 1 / K ≤ 1 / ‖z‖ := one_div_le_one_div_of_le hzpos hzK
         _ = ‖z‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have heq : ‖z ^ (-s) * Complex.Gamma s‖ =
      ‖z‖ ^ (-s.re) * Real.exp (z.arg * s.im) * ‖Complex.Gamma s‖ := by
    rw [norm_mul, Complex.norm_cpow_of_ne_zero hz]
    simp only [Complex.neg_re, Complex.neg_im]
    rw [show z.arg * -s.im = -(z.arg * s.im) by ring, Real.exp_neg,
      div_inv_eq_mul]
  have hg := gamma_lower452 s hlo hhi ht
  have hc : 0 ≤ Real.pi / (3 * Real.sqrt (2 * Real.pi)) := by positivity
  have hprod := mul_le_mul
    (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) hg
    (by positivity) (by positivity : 0 ≤ ‖z‖ ^ (-s.re) * Real.exp (z.arg * s.im))
  have he : Real.exp (-1) ≤ Real.exp ((z.arg - Real.pi / 2) * s.im) :=
    Real.exp_le_exp.mpr (by nlinarith [hgap])
  calc
    Real.pi / (3 * Real.sqrt (2 * Real.pi)) / K * Real.exp (-1)
        ≤ Real.pi / (3 * Real.sqrt (2 * Real.pi)) / K *
          Real.exp ((z.arg - Real.pi / 2) * s.im) :=
            mul_le_mul_of_nonneg_left he (by positivity)
    _ = (1 / K * Real.exp (z.arg * s.im)) *
        (Real.pi / (3 * Real.sqrt (2 * Real.pi)) * Real.exp (-(Real.pi * s.im / 2))) := by
      have heqexp : Real.exp ((z.arg - Real.pi / 2) * s.im) =
          Real.exp (z.arg * s.im) * Real.exp (-(Real.pi * s.im / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [heqexp]
      ring
    _ ≤ _ := by rw [heq]; exact hprod

end LeanLab.Linnik1951

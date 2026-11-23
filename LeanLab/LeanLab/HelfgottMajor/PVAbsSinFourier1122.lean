import Mathlib
import LeanLab.HelfgottMajor.PVLemmas1122

/-!
Route burst S68, burst-20261122, tag abs-sin-fourier.
Proof of the LEAF `PVLemmas1122.abs_sin_fourier`, the Fourier series of |sin t|,
`|sin t| = 2/π - (4/π) ∑_{k ≥ 1} cos(2kt)/(4k^2 - 1)`, Gradshteyn and Ryzhik 1.444.

Route: |sin| is continuous and π-periodic, so it descends to a continuous function on
`AddCircle π`. Its Fourier coefficients are computed on the period interval [0, π] where
|sin x| = sin x, by an explicit antiderivative of `exp(-2inx) sin x`, giving
`c_n = -2/(π(4n^2-1))`. These are summable, so Mathlib's
`has_pointwise_sum_fourier_series_of_summable` gives pointwise convergence. Pairing n with -n
gives the cosine series, and removing the n = 0 term gives the stated form.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVAbsSinFourier1122

open Real Complex

/-- The integer `4n^2 - 1` never vanishes, so the coefficients below are well defined. -/
theorem four_sq_sub_one_ne (n : ℤ) : (4 * (n : ℂ) ^ 2 - 1) ≠ 0 := by
  have h : (4 * n ^ 2 - 1 : ℤ) ≠ 0 := by
    intro h
    have h' : (2 * n - 1) * (2 * n + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 h' with h'' | h'' <;> omega
  exact_mod_cast h

/-- The coefficient integral of the Fourier series of |sin| on its period interval [0, π],
where |sin x| = sin x: `∫_0^π e^{-2inx} sin x dx = -2/(4n^2-1)`, by the antiderivative
`e^{-2inx}(cos x + 2in sin x)/(4n^2-1)`. -/
theorem coeff_integral (n : ℤ) :
    ∫ x in (0:ℝ)..π, Complex.exp (-2 * I * n * x) * Complex.sin x =
      -2 / (4 * (n : ℂ) ^ 2 - 1) := by
  have hd := four_sq_sub_one_ne n
  have hG : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-2 * I * n * y) *
      (1 / (4 * (n : ℂ) ^ 2 - 1) * Complex.cos y + 2 * I * n / (4 * (n : ℂ) ^ 2 - 1) *
        Complex.sin y)) (Complex.exp (-2 * I * n * x) * Complex.sin x) x := by
    intro x
    have he : HasDerivAt (fun z : ℂ => Complex.exp (-2 * I * n * z))
        (Complex.exp (-2 * I * n * x) * (-2 * I * n)) (x : ℂ) := by
      have := ((hasDerivAt_id (x : ℂ)).const_mul (-2 * I * n)).cexp
      simpa using this
    have ht : HasDerivAt (fun z : ℂ => 1 / (4 * (n : ℂ) ^ 2 - 1) * Complex.cos z +
        2 * I * n / (4 * (n : ℂ) ^ 2 - 1) * Complex.sin z)
        (1 / (4 * (n : ℂ) ^ 2 - 1) * -Complex.sin x +
          2 * I * n / (4 * (n : ℂ) ^ 2 - 1) * Complex.cos x) (x : ℂ) :=
      ((Complex.hasDerivAt_cos _).const_mul _).add ((Complex.hasDerivAt_sin _).const_mul _)
    have h2 := (he.mul ht).comp_ofReal
    refine h2.congr_deriv ?_
    have hA : 1 / (4 * (n : ℂ) ^ 2 - 1) * (4 * (n : ℂ) ^ 2 - 1) = 1 := one_div_mul_cancel hd
    linear_combination (Complex.exp (-2 * I * n * x) * Complex.sin x) * hA +
      (-4 * (n : ℂ) ^ 2 * (1 / (4 * (n : ℂ) ^ 2 - 1)) * Complex.exp (-2 * I * n * x) *
        Complex.sin x) * I_sq
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hexp : Complex.exp (-2 * I * n * (π : ℂ)) = 1 := by
    rw [show -2 * I * (n : ℂ) * (π : ℂ) = ((-n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hexp, Complex.cos_pi, Complex.sin_pi]
  simp
  field_simp
  ring

/-- The Fourier series of |sin t|, Gradshteyn and Ryzhik 1.444, exactly the statement of the
LEAF `PVLemmas1122.abs_sin_fourier`. PROVED by the route described in the module doc. -/
theorem abs_sin_fourier (t : ℝ) :
    HasSum (fun k : ℕ => 4 / π * (Real.cos (2 * ((k : ℝ) + 1) * t) / (4 * ((k : ℝ) + 1) ^ 2 - 1)))
      (2 / π - |Real.sin t|) := by
  have : Fact (0 < π) := ⟨pi_pos⟩
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have hper : Function.Periodic (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) π := by
    intro x; simp [Real.sin_add_pi]
  let F : C(AddCircle π, ℂ) := ⟨hper.lift, by
    have hc : Continuous (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) := by fun_prop
    exact hc.quotient_liftOn' _⟩
  have hF : ∀ x : ℝ, F (x : AddCircle π) = ((|Real.sin x| : ℝ) : ℂ) := fun x => rfl
  have hcoef : ∀ n : ℤ, fourierCoeff F n = -2 / (π * (4 * (n : ℂ) ^ 2 - 1)) := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have : ∫ x in (0:ℝ)..π, fourier (-n) (x : AddCircle π) • F x =
        ∫ x in (0:ℝ)..π, Complex.exp (-2 * I * n * x) * Complex.sin x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le pi_pos.le] at hx
      simp only [hF, fourier_coe_apply, smul_eq_mul]
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2), Complex.ofReal_sin]
      congr 2
      push_cast
      field_simp
    rw [this, coeff_integral, Complex.real_smul]
    have hd := four_sq_sub_one_ne n
    push_cast
    field_simp
  have hsum : Summable (fourierCoeff F) := by
    rw [show (fourierCoeff F) = fun n : ℤ => -2 / (π * (4 * (n : ℂ) ^ 2 - 1)) from funext hcoef]
    refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => 1 / (n : ℝ) ^ 2)
      (summable_one_div_int_pow.mpr one_lt_two) ?_
    have hfin : {n : ℤ | n = 0}.Finite := Set.finite_singleton 0
    filter_upwards [hfin.compl_mem_cofinite] with n hn
    have hn : n ≠ 0 := hn
    have h1 : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
    have h1' : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h1
    have hc : (-2 / (π * (4 * (n : ℂ) ^ 2 - 1))) = ((-2 / (π * (4 * (n : ℝ) ^ 2 - 1)) : ℝ) : ℂ) := by
      push_cast; ring
    have hpos : 0 < π * (4 * (n : ℝ) ^ 2 - 1) := mul_pos pi_pos (by linarith)
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_two, abs_of_pos hpos]
    rw [div_le_div_iff₀ hpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right pi_gt_three.le (show (0:ℝ) ≤ 4 * (n : ℝ) ^ 2 - 1 by
      linarith)]
  have hpt := has_pointwise_sum_fourier_series_of_summable hsum (t : AddCircle π)
  rw [hF] at hpt
  have h2 := hpt.nat_add_neg
  have hterm : ∀ m : ℕ, fourierCoeff F (m : ℤ) • fourier (m : ℤ) (t : AddCircle π) +
      fourierCoeff F (-(m : ℤ)) • fourier (-(m : ℤ)) (t : AddCircle π) =
      ((-4 / (π * (4 * (m : ℝ) ^ 2 - 1)) * Real.cos (2 * m * t) : ℝ) : ℂ) := by
    intro m
    rw [hcoef, hcoef, fourier_coe_apply, fourier_coe_apply]
    have e1 : 2 * (π : ℂ) * I * ((m : ℤ) : ℂ) * (t : ℂ) / π = ((2 * m * t : ℝ) : ℂ) * I := by
      push_cast; field_simp
    have e2 : 2 * (π : ℂ) * I * ((-(m : ℤ) : ℤ) : ℂ) * (t : ℂ) / π =
        -((2 * m * t : ℝ) : ℂ) * I := by
      push_cast; field_simp
    rw [e1, e2]
    have hcos := Complex.two_cos ((2 * m * t : ℝ) : ℂ)
    rw [← Complex.ofReal_cos] at hcos
    push_cast at hcos ⊢
    linear_combination (2 * (-(π : ℂ) + π * (m : ℂ) ^ 2 * 4)⁻¹) * hcos
  have h0 : fourierCoeff F ((0 : ℕ) : ℤ) • fourier ((0 : ℕ) : ℤ) (t : AddCircle π) =
      ((2 / π : ℝ) : ℂ) := by
    rw [hcoef]; simp
  simp only [hterm] at h2
  rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) by rfl, h0, ← Complex.ofReal_add,
    Complex.hasSum_ofReal] at h2
  have h3 := (hasSum_nat_add_iff' 1).mpr h2
  have h4 := h3.neg
  convert h4 using 1
  · funext k
    push_cast
    field_simp
  · simp
    field_simp
    ring

/-- The type of the proved theorem is exactly that of the LEAF in `PVLemmas1122`. -/
example : type_of% @abs_sin_fourier =
    type_of% @LeanLab.HelfgottMajor.PVLemmas1122.abs_sin_fourier := rfl

end LeanLab.HelfgottMajor.PVAbsSinFourier1122

#print axioms LeanLab.HelfgottMajor.PVAbsSinFourier1122.four_sq_sub_one_ne
#print axioms LeanLab.HelfgottMajor.PVAbsSinFourier1122.coeff_integral
#print axioms LeanLab.HelfgottMajor.PVAbsSinFourier1122.abs_sin_fourier

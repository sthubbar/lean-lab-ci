/-
P0070, p. 365, the complex power increment before equation 32.
The explicit minimum below has constant three in its second term.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Section6

namespace LeanLab.PerelliPintz1992.Section6
open Real Set MeasureTheory

/-- LEAF. Page 365, before 32: the complex power increment divided by rho is at most theta. -/
theorem zero_increment_le {θ : ℝ} {ρ : ℂ} (hθ : 0 ≤ θ) (hβ : ρ.re ≤ 1) (hρ : ρ ≠ 0) :
    ‖((((1 + θ : ℝ) : ℂ) ^ ρ - 1) / ρ)‖ ≤ θ := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ ρ / ρ
  let f' : ℝ → ℂ := fun x => (x : ℂ) ^ (ρ - 1)
  have hd : ∀ x ∈ Icc 1 (1 + θ), HasDerivWithinAt f (f' x) (Icc 1 (1 + θ)) x := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    have hh := (hasDerivAt_ofReal_cpow_const hxp.ne' hρ).div_const ρ
    have he : ρ * (x : ℂ) ^ (ρ - 1) / ρ = (x : ℂ) ^ (ρ - 1) := by field_simp
    rw [he] at hh
    exact hh.hasDerivWithinAt
  have hb : ∀ x ∈ Ico 1 (1 + θ), ‖f' x‖ ≤ (1 : ℝ) := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    dsimp only [f']
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp, Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by linarith)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (1 + θ) ⟨by linarith, le_rfl⟩
  dsimp only [f] at hh
  simp only [Complex.ofReal_one, Complex.one_cpow] at hh
  rw [← sub_div] at hh
  simpa using hh

/-- LEAF. Page 365, before 32: the power increment is bounded by the minimum
of theta and three divided by the norm of rho when theta is at most one. -/
theorem zero_increment_min_bound {θ : ℝ} {ρ : ℂ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hβ : ρ.re ≤ 1) (hρ : ρ ≠ 0) :
    ‖((((1 + θ : ℝ) : ℂ) ^ ρ - 1) / ρ)‖ ≤ min θ (3 / ‖ρ‖) := by
  refine le_min (zero_increment_le hθ hβ hρ) ?_
  rw [norm_div]
  apply div_le_div_of_nonneg_right ?_ (norm_nonneg ρ)
  have hbase : 0 < 1 + θ := by linarith
  have hp : ‖((1 + θ : ℝ) : ℂ) ^ ρ‖ ≤ 1 + θ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + θ by linarith) hβ
  have hh := norm_sub_le (((1 + θ : ℝ) : ℂ) ^ ρ) 1
  rw [norm_one] at hh
  linarith


/-- LEAF. Page 365, integration in the step from 31 to 32: the trivial kernel bound.
For z equal to rho plus conjugate rho prime minus one, its real part lies between minus one and one. -/
theorem zero_pair_integral_trivial {N : ℝ} {z : ℂ} (hN : 0 < N)
    (hz : -1 ≤ z.re) (hz' : z.re ≤ 1) :
    ‖∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (z - 1)‖ ≤ 10 * N ^ z.re := by
  have hab : N / 2 ≤ 3 * N := by linarith
  have hp2 : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (z.re - 1) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (-2 : ℝ) ≤ z.re - 1 by linarith)
    norm_num at hh ⊢
    exact hh
  have hpow : (N / 2) ^ (z.re - 1) ≤ 4 * N ^ (z.re - 1) := by
    rw [Real.div_rpow hN.le (by norm_num)]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).2
    nlinarith [Real.rpow_nonneg hN.le (z.re - 1)]
  have hb : ∀ x ∈ uIoc (N / 2) (3 * N), ‖(x : ℂ) ^ (z - 1)‖ ≤ 4 * N ^ (z.re - 1) := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hxp : 0 < x := by linarith [hx.1]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp, Complex.sub_re, Complex.one_re]
    exact (Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < N / 2)
      hx.1.le (by linarith : z.re - 1 ≤ 0)).trans hpow
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have he : N ^ (z.re - 1) * N = N ^ z.re := by
    rw [Real.rpow_sub hN, Real.rpow_one]
    field_simp
  calc
    _ ≤ 4 * N ^ (z.re - 1) * |3 * N - N / 2| := hh
    _ = 10 * (N ^ (z.re - 1) * N) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 3 * N - N / 2)]
      ring
    _ = _ := by rw [he]

/-- LEAF. Page 365, integration in the step from 31 to 32: cancellation in the
imaginary direction supplies the reciprocal difference of imaginary parts. -/
theorem zero_pair_integral_oscillatory {N : ℝ} {z : ℂ} (hN : 0 < N)
    (hz : -1 ≤ z.re) (hz' : z.re ≤ 1) (him : z.im ≠ 0) :
    ‖∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (z - 1)‖ ≤ 5 * N ^ z.re / |z.im| := by
  have hzne : z ≠ 0 := by intro he; exact him (by simpa [he])
  have hab : N / 2 ≤ 3 * N := by linarith
  have hi := integral_cpow (a := N / 2) (b := 3 * N) (r := z - 1) (Or.inr
    ⟨by intro he; apply hzne; linear_combination he,
      by rw [uIcc_of_le hab]; intro he; have hh := he.1; linarith⟩)
  rw [sub_add_cancel] at hi
  rw [hi, norm_div]
  have hthree : ‖((3 * N : ℝ) : ℂ) ^ z‖ ≤ 3 * N ^ z.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 3 * N),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hN.le]
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hz'
    simpa using mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hN.le z.re)
  have hhalf : ‖((N / 2 : ℝ) : ℂ) ^ z‖ ≤ 2 * N ^ z.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < N / 2),
      Real.div_rpow hN.le (by norm_num)]
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hz
    have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ z.re := by norm_num at hh ⊢; exact hh
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).2
    nlinarith [Real.rpow_nonneg hN.le z.re]
  have hnum : ‖((3 * N : ℝ) : ℂ) ^ z - ((N / 2 : ℝ) : ℂ) ^ z‖ ≤ 5 * N ^ z.re := by
    have hh := norm_sub_le (((3 * N : ℝ) : ℂ) ^ z) (((N / 2 : ℝ) : ℂ) ^ z)
    linarith
  calc
    _ ≤ 5 * N ^ z.re / ‖z‖ := div_le_div_of_nonneg_right hnum (norm_nonneg z)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr him)
      (Complex.abs_im_le_norm z)

/-- LEAF. Page 366, equation 32: the integral kernel has the minimum of the
trivial bound and the reciprocal imaginary difference bound. -/
theorem zero_pair_integral_min {N : ℝ} {z : ℂ} (hN : 0 < N)
    (hz : -1 ≤ z.re) (hz' : z.re ≤ 1) (him : z.im ≠ 0) :
    ‖∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (z - 1)‖ ≤
      10 * N ^ z.re * min 1 (1 / |z.im|) := by
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 10 * N ^ z.re)]
  apply le_min
  · simpa using zero_pair_integral_trivial hN hz hz'
  · have hh := zero_pair_integral_oscillatory hN hz hz' him
    have hp : 0 ≤ N ^ z.re / |z.im| := by positivity
    calc
      _ ≤ 5 * (N ^ z.re / |z.im|) := by convert hh using 1 <;> ring
      _ ≤ 10 * (N ^ z.re / |z.im|) := by linarith
      _ = _ := by ring


/-- LEAF. Equation 32, p. 366: the kernel with max denominator covers the diagonal too. -/
theorem zero_pair_integral_kernel {N : ℝ} {z : ℂ} (hN : 0 < N)
    (hz : -1 ≤ z.re) (hz' : z.re ≤ 1) :
    ‖∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (z - 1)‖ ≤
      10 * N ^ z.re / max 1 |z.im| := by
  by_cases him : |z.im| ≤ 1
  · rw [max_eq_left him, div_one]
    exact zero_pair_integral_trivial hN hz hz'
  · have hpos : 0 < |z.im| := by linarith [not_le.mp him]
    rw [max_eq_right (not_le.mp him).le]
    exact (zero_pair_integral_oscillatory hN hz hz' (abs_pos.mp hpos)).trans
      (div_le_div_of_nonneg_right (by nlinarith [Real.rpow_nonneg hN.le z.re]) hpos.le)

/-- LEAF. Equation 32, p. 366: the normalized integration kernel for two zero
parameters has the power N to beta plus beta prime minus two and the imaginary gap weight. -/
theorem zero_pair_kernel {N : ℝ} {ρ ρ' : ℂ} (hN : 0 < N)
    (hρ : 0 ≤ ρ.re) (hρ' : ρ.re ≤ 1) (hρ₂ : 0 ≤ ρ'.re) (hρ₂' : ρ'.re ≤ 1) :
    ‖(1 / (N : ℂ)) * ∫ x : ℝ in N / 2..3 * N, (x : ℂ) ^ (ρ + star ρ' - 2)‖ ≤
      10 * N ^ (ρ.re + ρ'.re - 2) / max 1 |ρ.im - ρ'.im| := by
  let z : ℂ := ρ + star ρ' - 1
  have hz : z.re = ρ.re + ρ'.re - 1 := by simp [z]
  have him : z.im = ρ.im - ρ'.im := by simp [z, sub_eq_add_neg]
  have he : ρ + star ρ' - 2 = z - 1 := by dsimp [z]; ring
  have hh := zero_pair_integral_kernel (z := z) hN (by rw [hz]; linarith)
    (by rw [hz]; linarith)
  rw [he, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  have hb := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1 / N by positivity)
  have hp : N ^ (ρ.re + ρ'.re - 2) = N ^ z.re / N := by
    rw [hz, show ρ.re + ρ'.re - 2 = (ρ.re + ρ'.re - 1) - 1 by ring,
      Real.rpow_sub hN, Real.rpow_one]
  calc
    _ ≤ 1 / N * (10 * N ^ z.re / max 1 |z.im|) := hb
    _ = _ := by rw [hp, him]; ring

end LeanLab.PerelliPintz1992.Section6

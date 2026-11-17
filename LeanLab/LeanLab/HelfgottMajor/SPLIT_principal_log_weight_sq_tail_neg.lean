import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long

/-!
Splitting the negative tail square energy of the logarithmic derivative weight,
`Decomp457b.principal_log_weight_sq_tail_neg`, which bounds the square energy on the half
line `t < -5` by twenty.

The weight is the logarithmic derivative of the Riemann zeta function at `-1/2 + it`
divided by `-1/2 + it`, so its square is the square modulus of that logarithmic derivative
divided by `1/4 + t ^ 2`.  On `t < -5` the denominator is at least `t ^ 2`, and the
logarithmic derivative is at most the envelope `log |t| + 7`; the square of the envelope
over `t ^ 2` is an elementary integral on `(5, ∞)` whose value is
`(log 5 ^ 2 + 16 log 5 + 65) / 5`, and that number is below twenty since `log 5 ≤ 1.7`.

The envelope is not available as a single estimate in the library, so it is cut into the
two inputs that the functional equation needs: the logarithmic derivative on the line of
real part three halves, where the Dirichlet series makes the real point the largest one,
and the digamma function on the line of real part minus one half, which is the growth of
the gamma factor.  The functional equation
`z'/z(s) = -z'/z(1-s) + log 2 pi - psi(s) + (pi/2) tan(pi s/2)`, the exact modulus
`‖tan(-pi/4 + i y)‖ ≤ 1`, `log 2 pi ≤ 2` and `pi/2 ≤ 1.571` turn those two inputs into the
envelope, with the constant `19/10 + 2 + 3/2 + 1.571 ≤ 7`.  That chain, the comparison of
the weight with the envelope, the integrability of the weight and the addition of the
three pieces into the budget twenty are all proved below; only the three steps stated as
leaves remain open.

No prime sum, no zero sum and no scale appears in the statement of any leaf.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

open Filter
open scoped Topology

/-- LEAF. The digamma input. The modulus of the digamma function on the line of real part
minus one half is at most `log |t| + 3/2` from height two on. This is the growth step of the
gamma factor in the functional equation, and it is the piece that no series expansion in
the library supplies. -/
theorem principal_log_weight_tail_neg_digamma_envelope (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 3 / 2 := by
  sorry

/-- LEAF. The zeta input. On the whole line of real part three halves the logarithmic
derivative of the Riemann zeta function is at most `19/10` in modulus. This is the first
input of the envelope: on that line the Dirichlet series for the logarithmic derivative is
dominated term by term by its value at the real point `3/2`, where the numeral is the one
the source prints. -/
theorem principal_log_weight_tail_neg_zeta_three_halves (y : ℝ) :
    ‖logDeriv riemannZeta ((((3 / 2 : ℝ)) : ℂ) + y * Complex.I)‖ ≤ 19 / 10 := by
  sorry

/-! ### Auxiliary lemmas for the elementary tail integral

`(log x + 7) ^ 2 / x ^ 2` has the primitive `-((log x) ^ 2 + 16 log x + 65) / x` on the
positive axis, because `P - P' = (log x + 7) ^ 2` for `P = A ^ 2 + 16 A + 65` and `A = log x`.
The primitive tends to zero at infinity, the squared envelope is dominated by `121 / x ^ (3/2)`,
and `log 5 ≤ 1.61`, so the integral on `(5, ∞)` is at most `(1.61 ^ 2 + 16 * 1.61 + 65) / 5 < 20`.
-/

/-- `log 5 ≤ 1.61`. -/
private theorem log_five_le_tail_neg : Real.log 5 ≤ 1.61 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 11, (1.61 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp 1.61 := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- The primitive of `(log x + 7) ^ 2 / x ^ 2` on the positive axis. -/
private theorem hasDerivAt_tail_neg_primitive (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -((Real.log y) ^ 2 + 16 * Real.log y + 65) / y)
      ((Real.log x + 7) ^ 2 / x ^ 2) x := by
  have hL : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hmul : HasDerivAt (fun y : ℝ => Real.log y * Real.log y)
      (x⁻¹ * Real.log x + Real.log x * x⁻¹) x := hL.mul hL
  have hN : HasDerivAt (fun y : ℝ => Real.log y * Real.log y + 16 * Real.log y + 65)
      (x⁻¹ * Real.log x + Real.log x * x⁻¹ + 16 * x⁻¹) x := by
    have h1 : HasDerivAt (fun y : ℝ => Real.log y * Real.log y + 16 * Real.log y)
        (x⁻¹ * Real.log x + Real.log x * x⁻¹ + 16 * x⁻¹) x :=
      hmul.add (hL.const_mul 16)
    exact h1.add_const 65
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx.ne'
  have h := hN.neg.mul hinv
  have hxne : x ≠ 0 := hx.ne'
  convert h using 1
  · funext y
    simp only [Pi.mul_apply, Pi.neg_apply]
    ring
  · field_simp
    simp only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    ring

/-- The primitive tends to `0` at infinity. -/
private theorem tendsto_tail_neg_primitive :
    Tendsto (fun y : ℝ => -((Real.log y) ^ 2 + 16 * Real.log y + 65) / y) atTop (𝓝 0) := by
  have h12 : Tendsto (fun y : ℝ => Real.log y / y ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hs : Tendsto (fun y : ℝ => (Real.log y) ^ 2 / y) atTop (𝓝 0) := by
    have h2 : Tendsto (fun y : ℝ => (Real.log y / y ^ (1 / 2 : ℝ)) ^ 2) atTop (𝓝 0) := by
      simpa using h12.pow 2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (le_of_lt hy)]
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hev : (fun y : ℝ => -((Real.log y) ^ 2 + 16 * Real.log y + 65) / y)
      =ᶠ[atTop] fun y =>
        -((Real.log y) ^ 2 / y) - 16 * (Real.log y / y) - 65 * y⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    field_simp
    ring
  rw [Filter.tendsto_congr' hev]
  have hfin := ((hs.neg).sub (h1.const_mul 16)).sub (hinv.const_mul 65)
  simpa using hfin

/-- Integrability of the squared envelope on `(5, ∞)`, dominated by `121 / x ^ (3/2)`. -/
private theorem integrableOn_tail_neg_envelope :
    IntegrableOn (fun x : ℝ => (Real.log x + 7) ^ 2 / x ^ 2) (Set.Ioi 5) := by
  have hmaj : IntegrableOn (fun x : ℝ => 121 * x ^ (-(3 / 2) : ℝ)) (Set.Ioi 5) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 5)).const_mul 121
  have hcont : ContinuousOn (fun x : ℝ => (Real.log x + 7) ^ 2 / x ^ 2) (Set.Ioi (5 : ℝ)) := by
    apply ContinuousOn.div
    · refine ContinuousOn.pow ?_ 2
      exact (Real.continuousOn_log.mono (fun y hy => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [Set.mem_Ioi.mp hy])).add continuousOn_const
    · exact ContinuousOn.pow continuousOn_id 2
    · intro x hx
      have hx0 : (0 : ℝ) < x := by linarith [Set.mem_Ioi.mp hx]
      positivity
  refine hmaj.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx5 : (5 : ℝ) < x := Set.mem_Ioi.mp hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have hh := Real.log_le_rpow_div (le_of_lt hx0) (by norm_num : (0 : ℝ) < 1 / 4)
    have h2 : x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) := by ring
    rwa [h2] at hh
  have hpos : (0 : ℝ) ≤ Real.log x + 7 := by
    have := Real.log_pos (by linarith : (1 : ℝ) < x)
    linarith
  have hbound : Real.log x + 7 ≤ 11 * x ^ (1 / 4 : ℝ) := by linarith
  have hsq : (Real.log x + 7) ^ 2 ≤ 121 * x ^ (1 / 2 : ℝ) := by
    have h11 : (0 : ℝ) ≤ 11 * x ^ (1 / 4 : ℝ) := by positivity
    have e : (11 * x ^ (1 / 4 : ℝ)) ^ 2 = 121 * x ^ (1 / 2 : ℝ) := by
      rw [mul_pow,
        show (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) by
          rw [sq, ← Real.rpow_add hx0]
          norm_num]
      norm_num
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (le_of_lt hx0)]
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have e2 : x ^ 2 = x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  rw [div_le_iff₀ hx2, e2]
  have e3 : 121 * (x ^ (3 / 2 : ℝ))⁻¹ * (x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ))
      = 121 * x ^ (1 / 2 : ℝ) := by
    field_simp
  rw [e3]
  exact hsq

/-- `∫_5^∞ (log x + 7)^2 / x^2 ≤ 20`. -/
private theorem integral_Ioi_five_tail_neg_envelope :
    ∫ x in Set.Ioi (5 : ℝ), (Real.log x + 7) ^ 2 / x ^ 2 ≤ 20 := by
  have hderiv : ∀ x ∈ Set.Ici (5 : ℝ),
      HasDerivAt (fun y : ℝ => -((Real.log y) ^ 2 + 16 * Real.log y + 65) / y)
        ((Real.log x + 7) ^ 2 / x ^ 2) x :=
    fun x hx => hasDerivAt_tail_neg_primitive x (by linarith [Set.mem_Ici.mp hx])
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv integrableOn_tail_neg_envelope
    tendsto_tail_neg_primitive
  rw [key]
  have hlog := log_five_le_tail_neg
  have hpos5 : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)
  have e : (0 : ℝ) - -((Real.log 5) ^ 2 + 16 * Real.log 5 + 65) / 5
      = ((Real.log 5) ^ 2 + 16 * Real.log 5 + 65) / 5 := by ring
  rw [e]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)]
  nlinarith

/-- LEAF. The elementary integral. The envelope squared over `t ^ 2` is integrable on the
half line `t < -5`, and its integral there is at most twenty. The integral is elementary,
`∫ t in (5, ∞), (log t + 7) ^ 2 / t ^ 2 = (log 5 ^ 2 + 16 log 5 + 65) / 5`, and that is
below twenty because `log 5 ≤ 1.7`. Both the finiteness and the value are needed below:
the finiteness to compare the two integrands, the value to add up the budget. -/
theorem principal_log_weight_tail_neg_majorant_integral :
    IntegrableOn (fun t : ℝ => (Real.log (-t) + 7) ^ 2 / t ^ 2) (Set.Iio (-5)) ∧
      (∫ t in Set.Iio (-5 : ℝ), (Real.log (-t) + 7) ^ 2 / t ^ 2) ≤ 20 := by
  have hA : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Ioi (5 : ℝ)) = Set.Iio (-5) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  have hint : IntegrableOn (fun t : ℝ => (Real.log (-t) + 7) ^ 2 / t ^ 2) (Set.Iio (-5)) := by
    have hmap := hA.integrableOn_map_iff (μ := volume)
      (f := fun x : ℝ => (Real.log x + 7) ^ 2 / x ^ 2) (s := Set.Ioi (5 : ℝ))
    rw [Measure.map_neg_eq_self (volume : Measure ℝ), hpre] at hmap
    refine (hmap.mp integrableOn_tail_neg_envelope).congr_fun (fun x _ => ?_) measurableSet_Iio
    simp only [Function.comp_apply, neg_sq]
  refine ⟨hint, ?_⟩
  have hsub : (∫ t in Set.Iio (-5 : ℝ), (Real.log (-t) + 7) ^ 2 / t ^ 2)
      = ∫ x in Set.Ioi (5 : ℝ), (Real.log x + 7) ^ 2 / x ^ 2 := by
    have hcomp := integral_comp_neg_Iic (-5 : ℝ)
      (f := fun x : ℝ => (Real.log x + 7) ^ 2 / x ^ 2)
    rw [show (-(-5) : ℝ) = 5 by norm_num] at hcomp
    rw [← integral_Iic_eq_integral_Iio (x := (-5 : ℝ))
      (f := fun t : ℝ => (Real.log (-t) + 7) ^ 2 / t ^ 2)]
    refine (setIntegral_congr_fun measurableSet_Iic (fun x _ => ?_)).trans hcomp
    simp only [Function.comp_apply, neg_sq]
  rw [hsub]
  exact integral_Ioi_five_tail_neg_envelope

/-- The squared norm of the weight, as the square modulus of the logarithmic derivative of
zeta on the left contour divided by `1/4 + t ^ 2`. -/
private theorem norm_principalLogWeight_sq (t : ℝ) :
    ‖principalLogWeight t‖ ^ 2 =
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 / (1 / 4 + t ^ 2) := by
  have hs : ‖((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [principalLogWeight, norm_div, div_pow, hs]

/-- `‖tan(-pi/4 + i y)‖ ≤ 1`: at real part `-pi/4` the sine and the cosine have real and
imaginary parts of equal size, so the modulus of their quotient is one. -/
private theorem norm_tan_neg_pi_div_four_le (y : ℝ) :
    ‖Complex.tan ((-(π / 4) : ℝ) + y * Complex.I)‖ ≤ 1 := by
  set x : ℝ := -(π / 4) with hx
  have hsx : Real.sin x ^ 2 = 1 / 2 := by
    rw [hx, Real.sin_neg, Real.sin_pi_div_four, neg_sq, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hcx : Real.cos x ^ 2 = 1 / 2 := by
    rw [hx, Real.cos_neg, Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hcos : Complex.cos (x + y * Complex.I) =
      ((Real.cos x * Real.cosh y : ℝ) : ℂ) + ((-(Real.sin x * Real.sinh y) : ℝ) : ℂ) *
        Complex.I := by
    rw [Complex.cos_add_mul_I]; push_cast; ring
  have hsin : Complex.sin (x + y * Complex.I) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) *
        Complex.I := by
    rw [Complex.sin_add_mul_I]; push_cast; ring
  have hnc : ‖Complex.cos (x + y * Complex.I)‖ ^ 2 =
      (Real.cosh y ^ 2 + Real.sinh y ^ 2) / 2 := by
    rw [hcos, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    ring_nf
    rw [hsx, hcx]; ring
  have hns : ‖Complex.sin (x + y * Complex.I)‖ ^ 2 =
      (Real.cosh y ^ 2 + Real.sinh y ^ 2) / 2 := by
    rw [hsin, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    ring_nf
    rw [hsx, hcx]; ring
  have hcpos : 0 < ‖Complex.cos (x + y * Complex.I)‖ := by
    have h1 : (0 : ℝ) < ‖Complex.cos (x + y * Complex.I)‖ ^ 2 := by
      rw [hnc]
      have hc := Real.one_le_cosh y
      have hs := sq_nonneg (Real.sinh y)
      nlinarith
    nlinarith [norm_nonneg (Complex.cos (x + y * Complex.I))]
  have heq : ‖Complex.sin (x + y * Complex.I)‖ = ‖Complex.cos (x + y * Complex.I)‖ := by
    have h := hns.trans hnc.symm
    have h2 : Real.sqrt (‖Complex.sin (x + y * Complex.I)‖ ^ 2) =
        Real.sqrt (‖Complex.cos (x + y * Complex.I)‖ ^ 2) := by rw [h]
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2
  rw [Complex.tan_eq_sin_div_cos, norm_div, div_le_one hcpos]
  exact le_of_eq heq

/-- The envelope on the left line from the two inputs. The chain is the functional equation
of `zeta'/zeta`, the exact modulus of `tan` at real part `-pi/4`, `log 2 pi ≤ 2`, `pi/2` at
most `1.571` and the triangle inequality, which give `19/10 + 2 + 3/2 + 1.571 ≤ 7`. -/
private theorem logDeriv_left_line_pointwise_seven
    (hzeta : ∀ y : ℝ,
      ‖logDeriv riemannZeta ((((3 / 2 : ℝ)) : ℂ) + y * Complex.I)‖ ≤ 19 / 10)
    (hpsi : ∀ t : ℝ, 2 ≤ |t| →
      ‖Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 3 / 2)
    (t : ℝ) (ht : 2 ≤ |t|) :
    ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 7 := by
  set s : ℂ := (-1 / 2 : ℂ) + t * Complex.I with hsdef
  have hsim : s.im = t := by simp [hsdef]
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n hn
    have h := congr_arg Complex.im hn
    rw [hsim] at h
    simp only [Complex.intCast_im] at h
    rw [h] at ht
    norm_num at ht
  have hz : riemannZeta s ≠ 0 := by
    have h := LeanLab.PNTPort.ZetaZeros.zeta_left_ne t
    rw [hsdef]
    convert h using 1
    push_cast
    ring
  have hFE := logDeriv_riemannZeta_one_sub (s := s) hint hz
  have hA : ‖logDeriv riemannZeta (1 - s)‖ ≤ 19 / 10 := by
    have e : 1 - s = (((3 / 2 : ℝ)) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
      rw [hsdef]; push_cast; ring
    rw [e]
    exact hzeta (-t)
  have hB : ‖Complex.log (2 * π)‖ ≤ 2 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
    exact LeanLab.PNTPort.ZetaZeros.log_two_pi_le
  have hC : ‖Complex.digamma s‖ ≤ Real.log |t| + 3 / 2 := by
    rw [hsdef]
    exact hpsi t ht
  have hD : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 1.571 := by
    have e : (π : ℂ) * s / 2 = ((-(π / 4) : ℝ) : ℂ) + ((π * t / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hsdef]; push_cast; ring
    rw [e, norm_mul]
    have ht1 := norm_tan_neg_pi_div_four_le (π * t / 2)
    have hp : ‖(π : ℂ) / 2‖ ≤ 1.571 := by
      have h2 : ‖((2 : ℂ))‖ = 2 := by norm_num
      rw [norm_div, h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      have := Real.pi_lt_d6
      linarith
    calc _ ≤ 1.571 * 1 := mul_le_mul hp ht1 (norm_nonneg _) (by norm_num)
      _ = 1.571 := by norm_num
  rw [hFE]
  calc ‖-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s +
        π / 2 * Complex.tan (π * s / 2)‖
      ≤ ‖logDeriv riemannZeta (1 - s)‖ + ‖Complex.log (2 * π)‖ + ‖Complex.digamma s‖ +
        ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add (by rw [norm_neg]) le_rfl))
            le_rfl)) le_rfl)
    _ ≤ 19 / 10 + 2 + (Real.log |t| + 3 / 2) + 1.571 := by gcongr
    _ ≤ Real.log |t| + 7 := by linarith

/-- The negative tail budget, assembled from the three leaves. -/
theorem principal_log_weight_sq_tail_neg_split :
    (∫ t in Set.Iio (-5), ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  obtain ⟨hmajint, hmajval⟩ := principal_log_weight_tail_neg_majorant_integral
  have henv : ∀ t : ℝ, 2 ≤ |t| →
      ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 7 :=
    logDeriv_left_line_pointwise_seven principal_log_weight_tail_neg_zeta_three_halves
      principal_log_weight_tail_neg_digamma_envelope
  have hintw : IntegrableOn (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) (Set.Iio (-5)) :=
    (MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two
      (by norm_num)).integrableOn
  have hmono : ∀ t ∈ Set.Iio (-5 : ℝ),
      ‖principalLogWeight t‖ ^ 2 ≤ (Real.log (-t) + 7) ^ 2 / t ^ 2 := by
    intro t ht
    have ht5 : t < -5 := ht
    have ht1 : t < 0 := by linarith
    have habs : |t| = -t := abs_of_neg ht1
    have hb := henv t (by rw [habs]; linarith)
    rw [habs] at hb
    have hnn : (0 : ℝ) ≤ ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ := norm_nonneg _
    have h1 : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        (Real.log (-t) + 7) ^ 2 := by
      simpa using pow_le_pow_left₀ hnn hb 2
    rw [norm_principalLogWeight_sq]
    have h2 : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
    have h3 : ‖logDeriv riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 / (1 / 4 + t ^ 2) ≤
        (Real.log (-t) + 7) ^ 2 / (1 / 4 + t ^ 2) :=
      div_le_div_of_nonneg_right h1 h2.le
    have ht2 : (0 : ℝ) < t ^ 2 := by nlinarith
    have h4 : (Real.log (-t) + 7) ^ 2 / (1 / 4 + t ^ 2) ≤ (Real.log (-t) + 7) ^ 2 / t ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) ht2 (by linarith)
    linarith
  exact (setIntegral_mono_on hintw hmajint measurableSet_Iio hmono).trans hmajval

end LeanLab.HelfgottMajor.Decomp457b

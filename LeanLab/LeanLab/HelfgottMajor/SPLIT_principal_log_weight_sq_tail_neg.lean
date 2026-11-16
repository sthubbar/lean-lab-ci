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

/-- LEAF. The elementary integral. The envelope squared over `t ^ 2` is integrable on the
half line `t < -5`, and its integral there is at most twenty. The integral is elementary,
`∫ t in (5, ∞), (log t + 7) ^ 2 / t ^ 2 = (log 5 ^ 2 + 16 log 5 + 65) / 5`, and that is
below twenty because `log 5 ≤ 1.7`. Both the finiteness and the value are needed below:
the finiteness to compare the two integrands, the value to add up the budget. -/
theorem principal_log_weight_tail_neg_majorant_integral :
    IntegrableOn (fun t : ℝ => (Real.log (-t) + 7) ^ 2 / t ^ 2) (Set.Iio (-5)) ∧
      (∫ t in Set.Iio (-5 : ℝ), (Real.log (-t) + 7) ^ 2 / t ^ 2) ≤ 20 := by
  sorry

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

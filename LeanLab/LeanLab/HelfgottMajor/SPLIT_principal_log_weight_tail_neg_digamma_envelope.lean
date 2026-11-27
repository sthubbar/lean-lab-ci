import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long

/-!
Splitting the digamma input `Decomp457b.principal_log_weight_tail_neg_digamma_envelope` of
the negative tail split of P0014, Helfgott, Major arcs for Goldbach's problem,
arXiv 1305.2897: for `2 ≤ |t|`, `‖ψ(-1/2 + it)‖ ≤ log |t| + 3/2`.

The statement is true but tight: numerically `‖ψ(-1/2 + 2i)‖ = 2.192474` against
`log 2 + 3/2 = 2.193147`, a margin of `0.00067` at `t = 2`, and the margin grows with `|t|`.
So the route must be sharp near height two.

Route, the gamma factor step of the paper, P0014 page 34 display 4.10, where Binet's formula
for the digamma function is quoted:
* the recurrence `ψ(s + 3) = ψ(s) + 1/s + 1/(s+1) + 1/(s+2)` at `s = -1/2 + it`, proved here
  from Mathlib's `Complex.digamma_apply_add_nat`;
* LEAF, Stirling with two correction terms at `w = 5/2 + it`:
  `‖ψ(w) - (log w - 1/(2w) - 1/(12 w^2))‖ ≤ 1/(120 (5/2)^4) = 2/9375`;
* LEAF, the elementary envelope: for `2 ≤ |t|` the explicit main term plus `2/9375` is at most
  `log |t| + 3/2`; numerically its worst margin is `0.00040`, at `t = 2`.
The parent follows by the triangle inequality. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Complex

/-! ### Helpers for the envelope leaf

The digamma input is reduced to the real-variable inequality
`‖M - S3‖ ≤ log|t| + 3/2 - 2/9375` for `2 ≤ |t|`, where `M` is the explicit Stirling main term
at `w = 5/2 + it` and `S3` the three recurrence terms.  The real and imaginary parts are computed
exactly, each is bounded by a monotone comparison at `u = |t| = 2`, and the two rational
comparisons are proved as polynomial identities with nonnegative coefficients in `u - 2`.
-/

namespace DigEnv

open Real

open Complex Real

private theorem log_w_im (t : ℝ) :
    (Complex.log ((5 / 2 : ℂ) + t * I)).im = Real.arctan (2 * t / 5) := by
  rw [Complex.log_im]
  set z : ℂ := (5 / 2 : ℂ) + t * I with hz
  have hzre : z.re = 5 / 2 := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  have hzpos : 0 < z.re := by rw [hzre]; norm_num
  have h1 : |z.arg| < π / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl hzpos
  obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
  have htan : Real.tan z.arg = t / (5 / 2) := by
    rw [Complex.tan_arg, hzim, hzre]
  have h2 : Real.tan (Real.arctan (2 * t / 5)) = t / (5 / 2) := by
    rw [Real.tan_arctan]; ring
  exact Real.tan_inj_of_lt_of_lt_pi_div_two h1a h1b
    (Real.neg_pi_div_two_lt_arctan _) (Real.arctan_lt_pi_div_two _) (by rw [htan, h2])

private theorem log_w_re (t : ℝ) :
    (Complex.log ((5 / 2 : ℂ) + t * I)).re = Real.log (t ^ 2 + 25 / 4) / 2 := by
  rw [Complex.log_re]
  have hnorm2 : ‖(5 / 2 : ℂ) + t * I‖ ^ 2 = t ^ 2 + 25 / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hnpos : 0 < ‖(5 / 2 : ℂ) + t * I‖ := by
    have := Complex.re_le_norm ((5 / 2 : ℂ) + t * I)
    have h : ((5 / 2 : ℂ) + t * I).re = 5 / 2 := by simp
    rw [h] at this
    linarith
  have hlog : Real.log (‖(5 / 2 : ℂ) + t * I‖ ^ 2) = 2 * Real.log ‖(5 / 2 : ℂ) + t * I‖ := by
    rw [Real.log_pow]; push_cast; ring
  rw [hnorm2] at hlog
  linarith

private theorem inv_vertical_re (a u : ℝ) :
    (((a : ℂ) + u * I)⁻¹).re = a / (a ^ 2 + u ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp
  ring

private theorem inv_vertical_im (a u : ℝ) :
    (((a : ℂ) + u * I)⁻¹).im = -u / (a ^ 2 + u ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp
  ring

private theorem normSq_w (t : ℝ) : Complex.normSq ((5 / 2 : ℂ) + t * I) = t ^ 2 + 25 / 4 := by
  rw [Complex.normSq_apply]; simp; ring

private theorem w_sq_re (t : ℝ) : (((5 / 2 : ℂ) + t * I) ^ 2).re = 25 / 4 - t ^ 2 := by
  rw [sq, Complex.mul_re]; simp; ring

private theorem w_sq_im (t : ℝ) : (((5 / 2 : ℂ) + t * I) ^ 2).im = 5 * t := by
  rw [sq, Complex.mul_im]; simp; ring

private theorem normSq_w_sq (t : ℝ) :
    Complex.normSq (((5 / 2 : ℂ) + t * I) ^ 2) = (t ^ 2 + 25 / 4) ^ 2 := by
  rw [← normSq_w t, map_pow]

/-- The real part of the main term minus the recurrence terms. -/
private theorem Z_re (t : ℝ) :
    (Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
        1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
      (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)).re
    = Real.log (t ^ 2 + 25 / 4) / 2
      - (5 / (4 * (t ^ 2 + 25 / 4)) + (25 / 4 - t ^ 2) / (12 * (t ^ 2 + 25 / 4) ^ 2)
          + (3 / 2) / (t ^ 2 + 9 / 4)) := by
  have hlog := log_w_re t
  have hw : ((5 / 2 : ℂ) + t * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hw2 : ((5 / 2 : ℂ) + t * I) ^ 2 ≠ 0 := pow_ne_zero 2 hw
  -- the `1 / (2 w)` term
  have h1 : (1 / (2 * ((5 / 2 : ℂ) + t * I))).re = 5 / (4 * (t ^ 2 + 25 / 4)) := by
    rw [show (1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))
        = (((1 / 2 : ℝ)) : ℂ) * ((5 / 2 : ℂ) + t * I)⁻¹ by
      rw [one_div, mul_inv_rev]; push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.inv_re, normSq_w]
    have hre : ((5 / 2 : ℂ) + t * I).re = 5 / 2 := by simp
    rw [hre]
    field_simp
    norm_num
  -- the `1 / (12 w^2)` term
  have h2 : (1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)).re
      = (25 / 4 - t ^ 2) / (12 * (t ^ 2 + 25 / 4) ^ 2) := by
    rw [show (1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)
        = (((1 / 12 : ℝ)) : ℂ) * (((5 / 2 : ℂ) + t * I) ^ 2)⁻¹ by
      rw [one_div, mul_inv_rev]; push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.inv_re, normSq_w_sq, w_sq_re]
    field_simp
  -- the three reciprocals
  have hr0 := inv_vertical_re (-1 / 2) t
  have hr1 := inv_vertical_re (1 / 2) t
  have hr2 := inv_vertical_re (3 / 2) t
  have h3 : (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹).re
      = (3 / 2) / (t ^ 2 + 9 / 4) := by
    have e0 : ((-1 / 2 : ℂ) + t * I) = (((-1 / 2 : ℝ)) : ℂ) + t * I := by push_cast; ring
    have e1 : ((1 / 2 : ℂ) + t * I) = (((1 / 2 : ℝ)) : ℂ) + t * I := by push_cast; ring
    have e2 : ((3 / 2 : ℂ) + t * I) = (((3 / 2 : ℝ)) : ℂ) + t * I := by push_cast; ring
    rw [e0, e1, e2, Complex.add_re, Complex.add_re, hr0, hr1, hr2]
    field_simp
    ring
  rw [Complex.sub_re, Complex.sub_re, Complex.sub_re, hlog, h1, h2, h3]
  ring

/-- The imaginary part of the main term minus the recurrence terms. -/
private theorem Z_im (t : ℝ) :
    (Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
        1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
      (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)).im
    = Real.arctan (2 * t / 5)
      + (t / (2 * (t ^ 2 + 25 / 4)) + 5 * t / (12 * (t ^ 2 + 25 / 4) ^ 2)
          + 2 * t / (t ^ 2 + 1 / 4) + t / (t ^ 2 + 9 / 4)) := by
  have hlog := log_w_im t
  have h1 : (1 / (2 * ((5 / 2 : ℂ) + t * I))).im = -t / (2 * (t ^ 2 + 25 / 4)) := by
    rw [show (1 : ℂ) / (2 * ((5 / 2 : ℂ) + t * I))
        = (((1 / 2 : ℝ)) : ℂ) * ((5 / 2 : ℂ) + t * I)⁻¹ by
      rw [one_div, mul_inv_rev]; push_cast; ring]
    rw [Complex.im_ofReal_mul, Complex.inv_im, normSq_w]
    have him : ((5 / 2 : ℂ) + t * I).im = t := by simp
    rw [him]
    field_simp
  have h2 : (1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)).im
      = -5 * t / (12 * (t ^ 2 + 25 / 4) ^ 2) := by
    rw [show (1 : ℂ) / (12 * ((5 / 2 : ℂ) + t * I) ^ 2)
        = (((1 / 12 : ℝ)) : ℂ) * (((5 / 2 : ℂ) + t * I) ^ 2)⁻¹ by
      rw [one_div, mul_inv_rev]; push_cast; ring]
    rw [Complex.im_ofReal_mul, Complex.inv_im, normSq_w_sq, w_sq_im]
    field_simp
  have hr0 := inv_vertical_im (-1 / 2) t
  have hr1 := inv_vertical_im (1 / 2) t
  have hr2 := inv_vertical_im (3 / 2) t
  have h3 : (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹).im
      = -2 * t / (t ^ 2 + 1 / 4) - t / (t ^ 2 + 9 / 4) := by
    have e0 : ((-1 / 2 : ℂ) + t * I) = (((-1 / 2 : ℝ)) : ℂ) + t * I := by push_cast; ring
    have e1 : ((1 / 2 : ℂ) + t * I) = (((1 / 2 : ℝ)) : ℂ) + t * I := by push_cast; ring
    have e2 : ((3 / 2 : ℂ) + t * I) = (((3 / 2 : ℝ)) : ℂ) + t * I := by push_cast; ring
    rw [e0, e1, e2, Complex.add_im, Complex.add_im, hr0, hr1, hr2]
    field_simp
    ring
  rw [Complex.sub_im, Complex.sub_im, Complex.sub_im, hlog, h1, h2, h3]
  ring

open Complex Real

/-- `x - x^3/3 ≤ arctan x` on the nonnegative axis. -/
private theorem arctan_lower (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.arctan x := by
  let f : ℝ → ℝ := fun t => Real.arctan t - t + t ^ 3 / 3
  have hd : ∀ t : ℝ, HasDerivAt f (t ^ 4 / (1 + t ^ 2)) t := by
    intro t
    have ha : HasDerivAt (fun s : ℝ => Real.arctan s) (1 / (1 + t ^ 2)) t :=
      Real.hasDerivAt_arctan t
    have hb : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have hc : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
      have h := (hasDerivAt_pow 3 t).div_const 3
      convert h using 1
      push_cast
      ring
    have h := (ha.sub hb).add hc
    refine h.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn f (Set.Ici 0) :=
    fun t _ => (hd t).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Ici 0)) :=
    fun t _ => (hd t).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ t ∈ interior (Set.Ici 0), 0 ≤ deriv f t := by
    intro t _
    rw [(hd t).deriv]
    positivity
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hnonneg
  have h0 : f 0 ≤ f x := hmono (Set.mem_Ici.mpr le_rfl) hx hx
  simp only [f, Real.arctan_zero] at h0
  linarith

/-- `arctan x ≤ x - x^3/3 + x^5/5` on the nonnegative axis. -/
private theorem arctan_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  let f : ℝ → ℝ := fun t => t - t ^ 3 / 3 + t ^ 5 / 5 - Real.arctan t
  have hd : ∀ t : ℝ, HasDerivAt f (t ^ 6 / (1 + t ^ 2)) t := by
    intro t
    have ha : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have hb : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
      have h := (hasDerivAt_pow 3 t).div_const 3
      convert h using 1
      push_cast
      ring
    have hc : HasDerivAt (fun s : ℝ => s ^ 5 / 5) (t ^ 4) t := by
      have h := (hasDerivAt_pow 5 t).div_const 5
      convert h using 1
      push_cast
      ring
    have hd0 : HasDerivAt (fun s : ℝ => Real.arctan s) (1 / (1 + t ^ 2)) t :=
      Real.hasDerivAt_arctan t
    have h := ((ha.sub hb).add hc).sub hd0
    refine h.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn f (Set.Ici 0) :=
    fun t _ => (hd t).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Ici 0)) :=
    fun t _ => (hd t).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ t ∈ interior (Set.Ici 0), 0 ≤ deriv f t := by
    intro t _
    rw [(hd t).deriv]
    positivity
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hnonneg
  have h0 : f 0 ≤ f x := hmono (Set.mem_Ici.mpr le_rfl) hx hx
  simp only [f, Real.arctan_zero] at h0
  linarith

/-- `log (1 - x) ≤ -x - x^2/2` for `x` in `[0,1)`. -/
private theorem log_one_sub_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 := by
  have h1 : (0:ℝ) < 1 - x := by linarith
  have h2 : (0:ℝ) < 1 + x := by linarith
  have hmul : Real.log (1 - x ^ 2) = Real.log (1 - x) + Real.log (1 + x) := by
    rw [← Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
    ring_nf
  have hA : Real.log (1 - x ^ 2) ≤ -x ^ 2 := by
    have hpos : (0:ℝ) < 1 - x ^ 2 := by nlinarith
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hB : x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
    have h := Real.le_log_one_add_of_nonneg hx0
    have hx2 : (0:ℝ) < x + 2 := by linarith
    have : x - x ^ 2 / 2 ≤ 2 * x / (x + 2) := by
      rw [le_div_iff₀ hx2]
      nlinarith
    linarith
  linarith

/-- `log (41/32) ≤ 0.2478364`. -/
private theorem log_41_32_le : Real.log (41 / 32) ≤ 0.2478364 := by
  have hlog5 := log_five_lt_d9
  have hlog2 := log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := log_four_eq
  have hmul : Real.log 5 = Real.log 4 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h54 : Real.log (5 / 4) ≤ 0.223143552 := by
    rw [hlog4] at hmul; linarith
  have hser := Real.abs_log_sub_add_sum_range_le (x := (-1/40 : ℝ)) (by norm_num) 5
  have habs : |((-1/40 : ℝ))| = 1/40 := by norm_num
  rw [habs] at hser
  have hval : (1:ℝ) - (-1/40) = 41/40 := by norm_num
  rw [hval] at hser
  have hSval : (∑ i ∈ Finset.range 5, ((-1/40 : ℝ)) ^ (i + 1) / ((i:ℝ) + 1))
      = -(37927853 / 1536000000) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [hSval] at hser
  have hrem : |((-1/40 : ℝ))| ^ (5 + 1) / (1 - |((-1/40 : ℝ))|) ≤ 1 / 3993600000 := by
    rw [habs]
    norm_num
  have h440 : Real.log (41/40) ≤ 0.0246927 := by
    have hle := (abs_le.mp hser).2
    linarith
  have hmul2 : Real.log (41/32) = Real.log (41/40) + Real.log (5/4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [hmul2]
  linarith

open Complex Real

example (u : ℝ) (hu : 2 ≤ u) : (0:ℝ) ≤ 4 * (u - 2) + 7 * (u - 2) ^ 3 + 9 * (u - 2) ^ 10 := by
  have hs0 : (0:ℝ) ≤ u - 2 := by linarith
  positivity

set_option maxHeartbeats 1000000 in
private theorem D_poly (u : ℝ) (hu : 2 ≤ u) :
    0 ≤ 5 / (4 * (u ^ 2 + 25 / 4)) + (25 / 4 - u ^ 2) / (12 * (u ^ 2 + 25 / 4) ^ 2)
        + (3 / 2) / (u ^ 2 + 9 / 4)
        + (25 * (u ^ 2 - 4) / (41 * u ^ 2)) / 2
        + (25 * (u ^ 2 - 4) / (41 * u ^ 2)) ^ 2 / 4 - 15286 / 42025 := by
  have hu0 : (0:ℝ) < u := by linarith
  have hden : (0:ℝ) < 504300 * u ^ 4 * (4 * u ^ 2 + 9) * (4 * u ^ 2 + 25) ^ 2 := by positivity
  have hid : (5 / (4 * (u ^ 2 + 25 / 4)) + (25 / 4 - u ^ 2) / (12 * (u ^ 2 + 25 / 4) ^ 2)
        + (3 / 2) / (u ^ 2 + 9 / 4)
        + (25 * (u ^ 2 - 4) / (41 * u ^ 2)) / 2
        + (25 * (u ^ 2 - 4) / (41 * u ^ 2)) ^ 2 / 4 - 15286 / 42025)
        * (504300 * u ^ 4 * (4 * u ^ 2 + 9) * (4 * u ^ 2 + 25) ^ 2)
      = 33611313248 * (u - 2) + 92254958504 * (u - 2) ^ 2 + 102423146184 * (u - 2) ^ 3
        + 66215343545 * (u - 2) ^ 4 + 28071737744 * (u - 2) ^ 5 + 8204382924 * (u - 2) ^ 6
        + 1679336192 * (u - 2) ^ 7 + 237000752 * (u - 2) ^ 8 + 22007040 * (u - 2) ^ 9
        + 1100352 * (u - 2) ^ 10 := by
    field_simp
    ring
  have hs0 : (0:ℝ) ≤ u - 2 := by linarith
  have hP : (0:ℝ) ≤ 33611313248 * (u - 2) + 92254958504 * (u - 2) ^ 2 + 102423146184 * (u - 2) ^ 3
        + 66215343545 * (u - 2) ^ 4 + 28071737744 * (u - 2) ^ 5 + 8204382924 * (u - 2) ^ 6
        + 1679336192 * (u - 2) ^ 7 + 237000752 * (u - 2) ^ 8 + 22007040 * (u - 2) ^ 9
        + 1100352 * (u - 2) ^ 10 := by positivity
  have h2 : (0:ℝ) ≤ (504300 * u ^ 4 * (4 * u ^ 2 + 9) * (4 * u ^ 2 + 25) ^ 2)
        * (5 / (4 * (u ^ 2 + 25 / 4)) + (25 / 4 - u ^ 2) / (12 * (u ^ 2 + 25 / 4) ^ 2)
        + (3 / 2) / (u ^ 2 + 9 / 4)
        + (25 * (u ^ 2 - 4) / (41 * u ^ 2)) / 2
        + (25 * (u ^ 2 - 4) / (41 * u ^ 2)) ^ 2 / 4 - 15286 / 42025) := by
    rw [mul_comm, hid]
    exact hP
  exact nonneg_of_mul_nonneg_right h2 hden

open Complex Real

set_option maxHeartbeats 2000000 in
private theorem M_poly (u : ℝ) (hu : 2 ≤ u) :
    0 ≤ 2929148 / 2143275
        - (u / (2 * (u ^ 2 + 25 / 4)) + 5 * u / (12 * (u ^ 2 + 25 / 4) ^ 2)
            + 2 * u / (u ^ 2 + 1 / 4) + u / (u ^ 2 + 9 / 4))
        - ((10 * (u - 2) / (8 * u + 25)) - (10 * (u - 2) / (8 * u + 25)) ^ 3 / 3
            + (10 * (u - 2) / (8 * u + 25)) ^ 5 / 5) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hden : (0:ℝ) < 2143275 * (8 * u + 25) ^ 5 * (4 * u ^ 2 + 1) * (4 * u ^ 2 + 9)
      * (4 * u ^ 2 + 25) ^ 2 := by positivity
  have hid : (2929148 / 2143275
        - (u / (2 * (u ^ 2 + 25 / 4)) + 5 * u / (12 * (u ^ 2 + 25 / 4) ^ 2)
            + 2 * u / (u ^ 2 + 1 / 4) + u / (u ^ 2 + 9 / 4))
        - ((10 * (u - 2) / (8 * u + 25)) - (10 * (u - 2) / (8 * u + 25)) ^ 3 / 3
            + (10 * (u - 2) / (8 * u + 25)) ^ 5 / 5))
        * (2143275 * (8 * u + 25) ^ 5 * (4 * u ^ 2 + 1) * (4 * u ^ 2 + 9) * (4 * u ^ 2 + 25) ^ 2)
      = 36835235279946887236 * (u - 2) + 107936860138517673024 * (u - 2) ^ 2
        + 149254816308727145392 * (u - 2) ^ 3 + 128942344989111864832 * (u - 2) ^ 4
        + 77384793352808219584 * (u - 2) ^ 5 + 33943526958026548224 * (u - 2) ^ 6
        + 11134444399985032320 * (u - 2) ^ 7 + 2744066845740754944 * (u - 2) ^ 8
        + 501785746579723776 * (u - 2) ^ 9 + 65721111632986112 * (u - 2) ^ 10
        + 5707902003283968 * (u - 2) ^ 11 + 271247452176384 * (u - 2) ^ 12
        + 2829178281984 * (u - 2) ^ 13 := by
    field_simp
    ring
  have hs0 : (0:ℝ) ≤ u - 2 := by linarith
  have hP : (0:ℝ) ≤ 36835235279946887236 * (u - 2) + 107936860138517673024 * (u - 2) ^ 2
        + 149254816308727145392 * (u - 2) ^ 3 + 128942344989111864832 * (u - 2) ^ 4
        + 77384793352808219584 * (u - 2) ^ 5 + 33943526958026548224 * (u - 2) ^ 6
        + 11134444399985032320 * (u - 2) ^ 7 + 2744066845740754944 * (u - 2) ^ 8
        + 501785746579723776 * (u - 2) ^ 9 + 65721111632986112 * (u - 2) ^ 10
        + 5707902003283968 * (u - 2) ^ 11 + 271247452176384 * (u - 2) ^ 12
        + 2829178281984 * (u - 2) ^ 13 := by positivity
  have h2 : (0:ℝ) ≤ (2143275 * (8 * u + 25) ^ 5 * (4 * u ^ 2 + 1) * (4 * u ^ 2 + 9)
      * (4 * u ^ 2 + 25) ^ 2)
        * (2929148 / 2143275
        - (u / (2 * (u ^ 2 + 25 / 4)) + 5 * u / (12 * (u ^ 2 + 25 / 4) ^ 2)
            + 2 * u / (u ^ 2 + 1 / 4) + u / (u ^ 2 + 9 / 4))
        - ((10 * (u - 2) / (8 * u + 25)) - (10 * (u - 2) / (8 * u + 25)) ^ 3 / 3
            + (10 * (u - 2) / (8 * u + 25)) ^ 5 / 5)) := by
    rw [mul_comm, hid]
    exact hP
  exact nonneg_of_mul_nonneg_right h2 hden

set_option maxHeartbeats 1000000 in
/-- The envelope for the real part: `log|w| - Q(u) <= log u + 0.1067565` on `u >= 2`. -/
private theorem delta_le (u : ℝ) (hu : 2 ≤ u) :
    Real.log (1 + 25 / (4 * u ^ 2)) / 2
      - (5 / (4 * (u ^ 2 + 25 / 4)) + (25 / 4 - u ^ 2) / (12 * (u ^ 2 + 25 / 4) ^ 2)
          + (3 / 2) / (u ^ 2 + 9 / 4)) ≤ 0.1067565 := by
  have hu0 : (0:ℝ) < u := by linarith
  have hx0 : 0 ≤ 25 * (u ^ 2 - 4) / (41 * u ^ 2) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  have hx1 : 25 * (u ^ 2 - 4) / (41 * u ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hfac : 1 + 25 / (4 * u ^ 2) = (41 / 16) * (1 - 25 * (u ^ 2 - 4) / (41 * u ^ 2)) := by
    field_simp
    ring
  have hzpos : (0:ℝ) < 1 - 25 * (u ^ 2 - 4) / (41 * u ^ 2) := by linarith
  have hlog : Real.log (1 + 25 / (4 * u ^ 2))
      = Real.log (41 / 16) + Real.log (1 - 25 * (u ^ 2 - 4) / (41 * u ^ 2)) := by
    rw [hfac, Real.log_mul (by norm_num) (ne_of_gt hzpos)]
  have hlogz := log_one_sub_le _ hx0 hx1
  have h4116 : Real.log (41 / 16) ≤ 0.9409836 := by
    have hm : Real.log (41 / 16) = Real.log 2 + Real.log (41 / 32) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h1 := log_41_32_le
    have h2 := log_two_lt_d9
    linarith
  have hD := D_poly u hu
  linarith

set_option maxHeartbeats 1000000 in
/-- The envelope for the imaginary part: `R(u) - arctan (5/(2u)) <= 0.47062` on `u >= 2`. -/
private theorem m_le (u : ℝ) (hu : 2 ≤ u) :
    (u / (2 * (u ^ 2 + 25 / 4)) + 5 * u / (12 * (u ^ 2 + 25 / 4) ^ 2)
        + 2 * u / (u ^ 2 + 1 / 4) + u / (u ^ 2 + 9 / 4)) - Real.arctan (5 / (2 * u)) ≤ 0.47062 := by
  have hu0 : (0:ℝ) < u := by linarith
  have hw0 : 0 ≤ 10 * (u - 2) / (8 * u + 25) := by
    apply div_nonneg _ (by positivity)
    linarith
  -- `arctan (5/4) = π/4 + arctan (1/9)`
  have h54 : Real.arctan (5 / 4) = Real.pi / 4 + Real.arctan (1 / 9) := by
    have h := Real.arctan_add (x := (1:ℝ)) (y := (1/9:ℝ)) (by norm_num)
    rw [Real.arctan_one] at h
    have e : (1 + 1/9) / (1 - 1 * (1/9)) = (5/4 : ℝ) := by norm_num
    rw [e] at h
    linarith
  -- `arctan (1/9) ≥ 242/2187`
  have h19 : (242/2187 : ℝ) ≤ Real.arctan (1 / 9) := by
    have h := arctan_lower (1/9) (by norm_num)
    have e : (1/9:ℝ) - (1/9)^3/3 = 242/2187 := by norm_num
    linarith
  -- `arctan (5/4) - arctan (5/(2u)) = arctan (10(u-2)/(8u+25))`
  have hsub : Real.arctan (5 / 4) - Real.arctan (5 / (2 * u)) = Real.arctan (10 * (u - 2) / (8 * u + 25)) := by
    have h5 : (0:ℝ) < 5/(2*u) := by apply div_pos (by norm_num); linarith
    have hsmall : (5/4:ℝ) * (-(5/(2*u))) < 1 := by nlinarith
    have h := Real.arctan_add (x := (5/4:ℝ)) (y := -(5/(2*u))) hsmall
    rw [Real.arctan_neg] at h
    have e : (5/4 + -(5/(2*u))) / (1 - (5/4) * -(5/(2*u))) = 10 * (u - 2) / (8 * u + 25) := by
      have hpos : (0:ℝ) < 1 - (5/4) * (-(5/(2*u))) := by nlinarith
      have hpos2 : (0:ℝ) < 8 * u + 25 := by linarith
      rw [div_eq_div_iff (ne_of_gt hpos) (ne_of_gt hpos2)]
      field_simp
      ring
    rw [e] at h
    linarith
  -- the arctan upper bound
  have hup := arctan_upper (10 * (u - 2) / (8 * u + 25)) hw0
  -- the polynomial certificate
  have hM := M_poly u hu
  -- the numeric constants
  have hpi := Real.pi_gt_d20
  linarith


set_option maxHeartbeats 1000000 in
/-- The real part of the main term minus the recurrence terms is nonnegative. -/
private theorem Z_re_nonneg (t : ℝ) (ht : 2 ≤ |t|) :
    0 ≤ (Real.log (t ^ 2 + 25 / 4) / 2
      - (5 / (4 * (t ^ 2 + 25 / 4)) + (25 / 4 - t ^ 2) / (12 * (t ^ 2 + 25 / 4) ^ 2)
          + (3 / 2) / (t ^ 2 + 9 / 4))) := by
  have hlog4 : Real.log 4 ≤ Real.log (t ^ 2 + 25 / 4) :=
    Real.log_le_log (by norm_num) (by nlinarith [sq_nonneg t])
  have hlog2 : (0.6931471803 : ℝ) ≤ Real.log 2 := log_two_gt_d9.le
  have hlog4e : Real.log 4 = 2 * Real.log 2 := log_four_eq
  have hC : (41 / 4 : ℝ) ≤ t ^ 2 + 25 / 4 := by nlinarith [sq_nonneg t, sq_abs t]
  have hB : (25 / 4 : ℝ) ≤ t ^ 2 + 9 / 4 := by nlinarith [sq_nonneg t, sq_abs t]
  have h1 : 5 / (4 * (t ^ 2 + 25 / 4)) ≤ 5 / 41 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hC]
  have h2 : (3 / 2) / (t ^ 2 + 9 / 4) ≤ 6 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hB]
  have h3 : (25 / 4 - t ^ 2) / (12 * (t ^ 2 + 25 / 4) ^ 2) ≤ 100 / 20172 := by
    rcases le_or_gt (t ^ 2) (25 / 4) with hle | hgt
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hC, hle]
    · have : (25 / 4 - t ^ 2) ≤ 0 := by linarith
      have : (25 / 4 - t ^ 2) / (12 * (t ^ 2 + 25 / 4) ^ 2) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg this (by positivity)
      linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- The imaginary part bound at nonnegative height. -/
private theorem im_abs_le_pos (u : ℝ) (hu : 2 ≤ u) :
    |Real.arctan (2 * u / 5)
      + (u / (2 * (u ^ 2 + 25 / 4)) + 5 * u / (12 * (u ^ 2 + 25 / 4) ^ 2)
          + 2 * u / (u ^ 2 + 1 / 4) + u / (u ^ 2 + 9 / 4))| ≤ Real.pi / 2 + 0.47062 := by
  have hu0 : (0:ℝ) < u := by linarith
  have h5 : (0:ℝ) < 5 / (2 * u) := by apply div_pos (by norm_num); linarith
  have harct : Real.arctan (2 * u / 5) = Real.pi / 2 - Real.arctan (5 / (2 * u)) := by
    have h := Real.arctan_inv_of_pos h5
    have e : (5 / (2 * u))⁻¹ = 2 * u / 5 := by field_simp
    rw [e] at h
    linarith
  have hm := m_le u hu
  have hR : 0 ≤ u / (2 * (u ^ 2 + 25 / 4)) + 5 * u / (12 * (u ^ 2 + 25 / 4) ^ 2)
      + 2 * u / (u ^ 2 + 1 / 4) + u / (u ^ 2 + 9 / 4) := by positivity
  have hpi2 := Real.arctan_lt_pi_div_two (5 / (2 * u))
  have hlow : -(Real.pi / 2 + 0.47062) ≤ Real.arctan (2 * u / 5)
      + (u / (2 * (u ^ 2 + 25 / 4)) + 5 * u / (12 * (u ^ 2 + 25 / 4) ^ 2)
          + 2 * u / (u ^ 2 + 1 / 4) + u / (u ^ 2 + 9 / 4)) := by
    rw [harct]
    linarith
  have hup : Real.arctan (2 * u / 5)
      + (u / (2 * (u ^ 2 + 25 / 4)) + 5 * u / (12 * (u ^ 2 + 25 / 4) ^ 2)
          + 2 * u / (u ^ 2 + 1 / 4) + u / (u ^ 2 + 9 / 4)) ≤ Real.pi / 2 + 0.47062 := by
    rw [harct]
    linarith
  exact abs_le.mpr ⟨hlow, hup⟩

set_option maxHeartbeats 2000000 in
/-- The main term minus the recurrence terms, bounded on `2 ≤ |t|`. -/
private theorem Z_norm_le (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
        1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
      (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖
      ≤ Real.log |t| + (3 / 2 - 2 / 9375) := by
  set Z : ℂ := Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
        1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
      (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹) with hZ
  have hpos : (0:ℝ) < |t| := by linarith [abs_nonneg t]
  have hre_eq : Z.re = Real.log (t ^ 2 + 25 / 4) / 2
      - (5 / (4 * (t ^ 2 + 25 / 4)) + (25 / 4 - t ^ 2) / (12 * (t ^ 2 + 25 / 4) ^ 2)
          + (3 / 2) / (t ^ 2 + 9 / 4)) := by
    rw [hZ]; exact Z_re t
  have him_eq : Z.im = Real.arctan (2 * t / 5)
      + (t / (2 * (t ^ 2 + 25 / 4)) + 5 * t / (12 * (t ^ 2 + 25 / 4) ^ 2)
          + 2 * t / (t ^ 2 + 1 / 4) + t / (t ^ 2 + 9 / 4)) := by
    rw [hZ]; exact Z_im t
  -- split the log
  have hfac : t ^ 2 + 25 / 4 = |t| ^ 2 * (1 + 25 / (4 * |t| ^ 2)) := by
    rw [show t ^ 2 = |t| ^ 2 by rw [sq_abs]]
    field_simp
  have hunit : (0:ℝ) < 1 + 25 / (4 * |t| ^ 2) := by positivity
  have hlogsplit : Real.log (t ^ 2 + 25 / 4) / 2
      = Real.log |t| + Real.log (1 + 25 / (4 * |t| ^ 2)) / 2 := by
    rw [hfac, Real.log_mul (by positivity) (ne_of_gt hunit), Real.log_pow]
    push_cast
    have : Real.log |t| * 2 / 2 = Real.log |t| := by ring
    linarith
  -- real part upper bound
  have hre_up : Z.re ≤ Real.log |t| + 0.1067565 := by
    rw [hre_eq, hlogsplit]
    have hsq : t ^ 2 = |t| ^ 2 := by rw [sq_abs]
    rw [hsq]
    linarith [delta_le |t| ht]
  have hre_nn : 0 ≤ Z.re := by
    rw [hre_eq]
    exact Z_re_nonneg t ht
  -- imaginary part bound
  have him_bd : |Z.im| ≤ Real.pi / 2 + 0.47062 := by
    rw [him_eq]
    rcases lt_or_ge t 0 with hneg | hge
    · have ht' : t = -|t| := by rw [abs_of_neg hneg]; ring
      have hodd : Real.arctan (2 * (-|t|) / 5)
          + ((-|t|) / (2 * ((-|t|) ^ 2 + 25 / 4)) + 5 * (-|t|) / (12 * ((-|t|) ^ 2 + 25 / 4) ^ 2)
              + 2 * (-|t|) / ((-|t|) ^ 2 + 1 / 4) + (-|t|) / ((-|t|) ^ 2 + 9 / 4))
          = -(Real.arctan (2 * |t| / 5)
          + (|t| / (2 * (|t| ^ 2 + 25 / 4)) + 5 * |t| / (12 * (|t| ^ 2 + 25 / 4) ^ 2)
              + 2 * |t| / (|t| ^ 2 + 1 / 4) + |t| / (|t| ^ 2 + 9 / 4))) := by
        rw [show (2 * (-|t|) / 5) = -(2 * |t| / 5) by ring, Real.arctan_neg]
        ring
      rw [ht', hodd, abs_neg]
      exact im_abs_le_pos |t| ht
    · have ht' : t = |t| := by rw [abs_of_nonneg hge]
      rw [ht']
      exact im_abs_le_pos |t| ht
  -- combine
  have hlog_pos : (0:ℝ) ≤ Real.log |t| := by
    have h1 : Real.log 1 ≤ Real.log |t| := Real.log_le_log (by norm_num) (by linarith)
    simpa using h1
  have hA : (0:ℝ) ≤ Real.log |t| + 0.1067565 := by linarith
  have hK : (0:ℝ) ≤ Real.pi / 2 + 0.47062 := by linarith [Real.pi_pos]
  have hsq : ‖Z‖ ^ 2 = Z.re ^ 2 + Z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h1 : Z.re ^ 2 ≤ (Real.log |t| + 0.1067565) ^ 2 := by
    nlinarith [hre_nn, hre_up, hA]
  have h2 : Z.im ^ 2 ≤ (Real.pi / 2 + 0.47062) ^ 2 := by
    have := abs_le.mp him_bd
    nlinarith [this.1, this.2, hK]
  have hlog_ge : (0.6931471803 : ℝ) ≤ Real.log |t| := by
    have h1 : Real.log 2 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
    linarith [log_two_gt_d9]
  have hK2 : (Real.pi / 2 + 0.47062) ^ 2 ≤ 4.167381 := by
    nlinarith [Real.pi_gt_d20, Real.pi_lt_d20, Real.pi_pos]
  have hc1 : (1.393 : ℝ) ≤ 3 / 2 - 2 / 9375 - 0.1067565 := by norm_num
  have hc2 : (2.9928 : ℝ) ≤ 2 * 0.6931471803 + (3 / 2 - 2 / 9375) + 0.1067565 := by norm_num
  have hprod : (4.167381 : ℝ) ≤ (3 / 2 - 2 / 9375 - 0.1067565)
      * (2 * 0.6931471803 + (3 / 2 - 2 / 9375) + 0.1067565) := by
    have hm := mul_le_mul hc1 hc2 (by norm_num : (0:ℝ) ≤ 2.9928)
      (by linarith : (0:ℝ) ≤ 3 / 2 - 2 / 9375 - 0.1067565)
    have hv : (4.167381 : ℝ) ≤ 1.393 * 2.9928 := by norm_num
    exact le_trans hv hm
  have hexp : (Real.log |t| + (3 / 2 - 2 / 9375)) ^ 2 - (Real.log |t| + 0.1067565) ^ 2
      = (3 / 2 - 2 / 9375 - 0.1067565)
        * (2 * Real.log |t| + (3 / 2 - 2 / 9375) + 0.1067565) := by ring
  have hcomb : Z.re ^ 2 + Z.im ^ 2 ≤ (Real.log |t| + (3 / 2 - 2 / 9375)) ^ 2 := by
    nlinarith [h1, h2, hK2, hprod, hexp, hlog_ge]
  have hgoal : ‖Z‖ ^ 2 ≤ (Real.log |t| + (3 / 2 - 2 / 9375)) ^ 2 := by
    rw [hsq]; exact hcomb
  calc ‖Z‖ = Real.sqrt (‖Z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg Z)).symm
    _ ≤ Real.sqrt ((Real.log |t| + (3 / 2 - 2 / 9375)) ^ 2) := Real.sqrt_le_sqrt hgoal
    _ = Real.log |t| + (3 / 2 - 2 / 9375) := Real.sqrt_sq (by positivity)

end DigEnv


/-- LEAF: Stirling's expansion of the digamma function with two correction terms, the gamma
factor step of P0014 page 34 display 4.10, where Binet's formula DLMF 5.9.13 to 5.9.15 is
quoted, specialised to the line of real part five halves. With
`ψ(w) = log w - 1/(2w) - ∫_0^∞ f(x) e^{-wx} dx`, `f(x) = 1/(e^x - 1) - 1/x + 1/2`, DLMF 5.9.13,
and `0 ≤ x/12 - f(x) ≤ x^3/720` for `x > 0`, the remainder after `-1/(12 w^2)` is at most
`∫_0^∞ x^3/720 e^{-(5/2)x} dx = 1/(120 (5/2)^4) = 2/9375` in modulus.
Numerically the true remainder is at most `0.37` of the bound on this line.
Class HARD: needs the Binet Laplace form of digamma and the Laplace transform estimate. -/
theorem tail_neg_digamma_stirling_five_half (t : ℝ) :
    ‖Complex.digamma ((5 / 2 : ℂ) + t * I) -
        (Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2))‖ ≤ 2 / 9375 := by
  sorry

/-- LEAF: the elementary envelope closing the gamma factor step of P0014 page 34 display
4.10 on the line of real part minus one half. With `s = -1/2 + it` and `w = s + 3`, the
explicit Stirling main term `log w - 1/(2w) - 1/(12 w^2)` minus the recurrence terms
`1/s + 1/(s+1) + 1/(s+2)`, plus the remainder budget `2/9375`, is at most `log |t| + 3/2`
for `2 ≤ |t|`. Numerically the worst margin is `0.00040`, at `|t| = 2`, rising to `0.38`
by `|t| = 3`; so near height two the argument of `w` and the logarithm need about four
correct digits. Class HARD: a sharp real variable inequality on an unbounded range. -/
theorem tail_neg_digamma_main_term_envelope (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.log ((5 / 2 : ℂ) + t * I) - 1 / (2 * ((5 / 2 : ℂ) + t * I)) -
          1 / (12 * ((5 / 2 : ℂ) + t * I) ^ 2) -
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹)‖ +
      2 / 9375 ≤ Real.log |t| + 3 / 2 := by
  have h := DigEnv.Z_norm_le t ht
  linarith

/-- The recurrence step, proved: `ψ(-1/2 + it + 3) = ψ(-1/2 + it) + Σ_{k<3} 1/(-1/2 + it + k)`. -/
theorem tail_neg_digamma_recurrence (t : ℝ) :
    Complex.digamma ((5 / 2 : ℂ) + t * I) =
      Complex.digamma ((-1 / 2 : ℂ) + t * I) +
        (((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹) := by
  have hs : ∀ m : ℕ, ((-1 / 2 : ℂ) + t * I) ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    simp at h
    have h2 : (2 : ℝ) * m = 1 := by linarith
    have h3 : (2 * m : ℕ) = 1 := by exact_mod_cast h2
    omega
  have h := Complex.digamma_apply_add_nat hs 3
  have e : ((-1 / 2 : ℂ) + t * I) + ((3 : ℕ) : ℂ) = (5 / 2 : ℂ) + t * I := by
    push_cast; ring
  rw [e] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  ring_nf

/-- The parent `principal_log_weight_tail_neg_digamma_envelope`, assembled from the two
leaves and the recurrence by the triangle inequality. -/
theorem principal_log_weight_tail_neg_digamma_envelope_of_leaves (t : ℝ) (ht : 2 ≤ |t|) :
    ‖Complex.digamma ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤ Real.log |t| + 3 / 2 := by
  have hrec := tail_neg_digamma_recurrence t
  have hS := tail_neg_digamma_stirling_five_half t
  have hM := tail_neg_digamma_main_term_envelope t ht
  set w : ℂ := (5 / 2 : ℂ) + t * I
  set M : ℂ := Complex.log w - 1 / (2 * w) - 1 / (12 * w ^ 2)
  set S3 : ℂ := ((-1 / 2 : ℂ) + t * I)⁻¹ + ((1 / 2 : ℂ) + t * I)⁻¹ + ((3 / 2 : ℂ) + t * I)⁻¹
  have hd : Complex.digamma ((-1 / 2 : ℂ) + t * I) =
      (Complex.digamma w - M) + (M - S3) := by
    rw [hrec]; ring
  rw [hd]
  calc ‖(Complex.digamma w - M) + (M - S3)‖
      ≤ ‖Complex.digamma w - M‖ + ‖M - S3‖ := norm_add_le _ _
    _ ≤ 2 / 9375 + ‖M - S3‖ := by gcongr
    _ ≤ Real.log |t| + 3 / 2 := by linarith

end LeanLab.HelfgottMajor.Decomp457b

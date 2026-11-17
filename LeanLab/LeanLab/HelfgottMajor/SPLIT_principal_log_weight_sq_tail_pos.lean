import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long

/-!
Splitting the positive tail energy `principal_log_weight_sq_tail_pos`, the square energy of the
logarithmic derivative weight on `5 < t` bounded by twenty.

The tail is cut once more, at height eight.  On the near piece `5 < t ≤ 8` the interval is short
and only the size of the weight is paid for; on the far piece `8 < t` only the decay is paid for.
Both pieces are compared against the same elementary majorant `(2 log t + 3) ^ 2 / t ^ 2`, whose
primitive `-((2 log t) ^ 2 + 20 log t + 29) / t` gives the two numerical values `3.322` and
`10.988`, and the two budgets four and sixteen add up to twenty.

Every leaf below is one step of that comparison: the pointwise square bound, integrability of the
majorant on each piece, and the two numerical integrals.  The partition identity, the monotone
comparison on each piece and the final addition are proved here, leaving no gap.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

/-- LEAF. The pointwise square bound on the positive tail: for `5 < t` the square of the
logarithmic derivative weight is at most the elementary majorant `(2 log t + 3) ^ 2 / t ^ 2`.
This is the analytic step, the size of `logDeriv riemannZeta` at `-1/2 + i t` against the size of
`-1/2 + i t`, and it carries all the arithmetic content of the bound. -/
theorem tail_pos_pointwise_sq (t : ℝ) (ht : 5 < t) :
    ‖principalLogWeight t‖ ^ 2 ≤ (2 * Real.log t + 3) ^ 2 / t ^ 2 := by
  sorry

/-- LEAF. Integrability of the majorant on the near piece `5 < t ≤ 8`.  The majorant is dominated
by a negative power of `t`, so it is integrable on the short interval; this is the hypothesis that
lets the near piece be compared with the weight. -/
theorem tail_pos_majorant_integrableOn_head :
    IntegrableOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioc 5 8) := by
  have hcont : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Icc 5 8) := by
    have hlog : ContinuousOn Real.log (Set.Icc (5 : ℝ) 8) :=
      Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : (5 : ℝ) ≤ x := hx.1
        rintro rfl
        norm_num at h1)
    have hnum : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2) (Set.Icc (5 : ℝ) 8) :=
      ((hlog.const_mul 2).add continuousOn_const).pow 2
    exact hnum.div (continuousOn_id.pow 2) (by
      intro x hx
      have h1 : (5 : ℝ) ≤ x := hx.1
      intro h
      have hx0 : x = 0 := sq_eq_zero_iff.mp h
      linarith)
  exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

/-- The power `t ^ (1/2)` divided by `t ^ 2` is `t ^ (-(3/2))`. -/
private lemma tail_pos_rpow_half_div_sq (t : ℝ) (ht : 0 < t) :
    t ^ (1 / 2 : ℝ) / t ^ 2 = t ^ (-(3 / 2) : ℝ) := by
  rw [div_eq_mul_inv, show (t ^ 2 : ℝ) = t ^ (2 : ℝ) by rw [Real.rpow_two],
    ← Real.rpow_neg ht.le (2 : ℝ), ← Real.rpow_add ht]
  norm_num

/-- The pointwise domination of the majorant by `121 t ^ (-(3/2))` on `8 < t`.  The logarithm
is paid for by a fourth root, which leaves the negative power `-(3/2)` of `t` behind. -/
private lemma tail_pos_majorant_le_rpow (t : ℝ) (ht : 8 < t) :
    (2 * Real.log t + 3) ^ 2 / t ^ 2 ≤ 121 * t ^ (-(3 / 2) : ℝ) := by
  have ht0 : 0 < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlog4 : Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 4)
    calc Real.log t ≤ t ^ (1 / 4 : ℝ) / (1 / 4) := h
      _ = 4 * t ^ (1 / 4 : ℝ) := by ring
  have hpow1 : (1 : ℝ) ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hlogpos : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hb : 2 * Real.log t + 3 ≤ 11 * t ^ (1 / 4 : ℝ) := by nlinarith
  have hb0 : 0 ≤ 2 * Real.log t + 3 := by linarith
  have hsq : (11 * t ^ (1 / 4 : ℝ)) ^ 2 = 121 * t ^ (1 / 2 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast ht0.le]
    norm_num
  have hsqle : (2 * Real.log t + 3) ^ 2 ≤ 121 * t ^ (1 / 2 : ℝ) := by
    nlinarith [hb, hb0, hsq, sq_nonneg (11 * t ^ (1 / 4 : ℝ)),
      sq_nonneg (2 * Real.log t + 3 - 11 * t ^ (1 / 4 : ℝ))]
  have hstep : (2 * Real.log t + 3) ^ 2 / t ^ 2 ≤ 121 * t ^ (1 / 2 : ℝ) / t ^ 2 :=
    div_le_div_of_nonneg_right hsqle (by positivity)
  have heq : 121 * t ^ (1 / 2 : ℝ) / t ^ 2 = 121 * t ^ (-(3 / 2) : ℝ) := by
    rw [show 121 * t ^ (1 / 2 : ℝ) / t ^ 2 = 121 * (t ^ (1 / 2 : ℝ) / t ^ 2) by ring,
      tail_pos_rpow_half_div_sq t ht0]
  linarith [hstep, heq.le, heq.ge]

/-- LEAF. Integrability of the majorant on the far piece `8 < t`.  Here the decay of the majorant
is what is paid for, and again a negative power of `t` dominates it; this is the hypothesis that
lets the far piece be compared with the weight. -/
theorem tail_pos_majorant_integrableOn_far :
    IntegrableOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioi 8) := by
  have hmaj : IntegrableOn (fun t : ℝ => 121 * t ^ (-(3 / 2) : ℝ)) (Set.Ioi 8) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-(3 / 2) : ℝ)) (c := 8) (by norm_num)
      (by norm_num)).const_mul 121
  have hcont : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioi 8) := by
    have hlog : ContinuousOn Real.log (Set.Ioi (8 : ℝ)) :=
      Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : (8 : ℝ) < x := hx
        rintro rfl
        norm_num at h1)
    have hnum : ContinuousOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2) (Set.Ioi (8 : ℝ)) :=
      ((hlog.const_mul 2).add continuousOn_const).pow 2
    exact hnum.div (continuousOn_id.pow 2) (by
      intro x hx
      have h1 : (8 : ℝ) < x := hx
      intro h
      have hx0 : x = 0 := sq_eq_zero_iff.mp h
      linarith)
  refine Integrable.mono' hmaj (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hnn : (0 : ℝ) ≤ (2 * Real.log t + 3) ^ 2 / t ^ 2 := by
    have h1 : (0 : ℝ) < t := by linarith [Set.mem_Ioi.mp ht]
    positivity
  rw [Real.norm_of_nonneg hnn]
  exact tail_pos_majorant_le_rpow t ht

/-- The primitive of the majorant: differentiating `-((2 log t)^2 + 20 log t + 29) / t` gives
`(2 log t + 3)^2 / t^2`. -/
private lemma hasDerivAt_tail_pos_primitive (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => -(((2 * Real.log s) ^ 2 + 20 * Real.log s + 29) / s))
      ((2 * Real.log t + 3) ^ 2 / t ^ 2) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.log s) (2 * t⁻¹) t := hlog.const_mul 2
  have h4 : HasDerivAt (fun s : ℝ => 20 * Real.log s) (20 * t⁻¹) t := hlog.const_mul 20
  have hA := ((h2.pow 2).add h4).add_const 29
  have hq := hA.div (hasDerivAt_id t) ht.ne'
  refine (hq.neg).congr_deriv ?_
  norm_num
  field_simp
  ring

/-- The logarithm squared over the identity tends to zero. -/
private lemma tail_pos_tendsto_log_sq_div (n : ℕ) :
    Filter.Tendsto (fun t : ℝ => Real.log t ^ n / t) Filter.atTop (nhds 0) :=
  (Real.isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero

/-- The primitive of the majorant tends to zero at infinity. -/
private lemma tendsto_tail_pos_primitive :
    Filter.Tendsto (fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t)) Filter.atTop (nhds 0) := by
  have h2 : Filter.Tendsto (fun t : ℝ => (2 * Real.log t) ^ 2 / t) Filter.atTop (nhds 0) := by
    have hbase := (tail_pos_tendsto_log_sq_div 2).const_mul (4 : ℝ)
    have hfun : (fun t : ℝ => (2 * Real.log t) ^ 2 / t)
        = fun t : ℝ => 4 * (Real.log t ^ 2 / t) := by
      funext t
      ring
    rw [hfun]
    simpa using hbase
  have h20 : Filter.Tendsto (fun t : ℝ => 20 * Real.log t / t) Filter.atTop (nhds 0) := by
    have hbase := (tail_pos_tendsto_log_sq_div 1).const_mul (20 : ℝ)
    have hfun : (fun t : ℝ => 20 * Real.log t / t)
        = fun t : ℝ => 20 * (Real.log t ^ 1 / t) := by
      funext t
      ring
    rw [hfun]
    simpa using hbase
  have h29 : Filter.Tendsto (fun t : ℝ => 29 / t) Filter.atTop (nhds 0) := by
    have hbase := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (29 : ℝ)
    have hfun : (fun t : ℝ => 29 / t) = fun t : ℝ => 29 * t⁻¹ := by
      funext t
      rw [div_eq_mul_inv]
    rw [hfun]
    simpa using hbase
  have hsum := ((h2.add h20).add h29).neg
  have hfun : (fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
      = fun t : ℝ => -((2 * Real.log t) ^ 2 / t + 20 * Real.log t / t + 29 / t) := by
    funext t
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
  rw [hfun]
  simpa using hsum

/-- The value of the majorant integral on the far piece, from the primitive. -/
private lemma integral_tail_pos_far :
    (∫ t in Set.Ioi (8 : ℝ), (2 * Real.log t + 3) ^ 2 / t ^ 2)
      = (4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29) / 8 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
    (f' := fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (a := 8) (m := 0)
    (fun x hx => hasDerivAt_tail_pos_primitive x (by linarith [Set.mem_Ici.mp hx]))
    tail_pos_majorant_integrableOn_far tendsto_tail_pos_primitive
  rw [h]
  ring

/-- The value of the majorant integral on the near piece, from the primitive. -/
private lemma integral_tail_pos_head :
    (∫ t in Set.Ioc (5 : ℝ) 8, (2 * Real.log t + 3) ^ 2 / t ^ 2)
      = (4 * (Real.log 5) ^ 2 + 20 * Real.log 5 + 29) / 5 -
        (4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29) / 8 := by
  have hle : (5 : ℝ) ≤ 8 := by norm_num
  rw [← intervalIntegral.integral_of_le hle]
  have hint : IntervalIntegrable (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) volume 5 8 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr tail_pos_majorant_integrableOn_head
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -(((2 * Real.log t) ^ 2 + 20 * Real.log t + 29) / t))
    (f' := fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (a := 5) (b := 8)
    (fun x hx => hasDerivAt_tail_pos_primitive x (by
      rw [Set.uIcc_of_le hle] at hx
      have h1 : (5 : ℝ) ≤ x := hx.1
      linarith))
    hint
  rw [h]
  ring

/-- The logarithm of five is at most `1.637`, from `log 5 = log (5/4) + 2 log 2`. -/
private lemma tail_pos_log_five_le : Real.log 5 ≤ 1.637 := by
  have hsplit : Real.log 5 = Real.log (5 / 4) + Real.log 4 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h54 : Real.log (5 / 4) ≤ 5 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  nlinarith [Real.log_two_lt_d9, hsplit, h54, h4]

/-- The logarithm of eight is three times the logarithm of two. -/
private lemma tail_pos_log_eight_eq : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  ring

/-- The elementary majorant at `log 8` is at most `128`. -/
private lemma tail_pos_A_log_eight_upper :
    4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29 ≤ 128 := by
  have heq := tail_pos_log_eight_eq
  have h1 : Real.log 8 ≤ 3 * 0.6931471808 := by
    rw [heq]
    nlinarith [Real.log_two_lt_d9]
  have h0 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- The elementary majorant at `log 8` is at least `87.8`. -/
private lemma tail_pos_A_log_eight_lower :
    87.8 ≤ 4 * (Real.log 8) ^ 2 + 20 * Real.log 8 + 29 := by
  have heq := tail_pos_log_eight_eq
  have h1 : 3 * 0.6931471803 ≤ Real.log 8 := by
    rw [heq]
    nlinarith [Real.log_two_gt_d9]
  have h0 : 0 ≤ Real.log 8 := le_trans (by norm_num) h1
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- The elementary majorant at `log 5` is at most `72.5`. -/
private lemma tail_pos_A_log_five_upper :
    4 * (Real.log 5) ^ 2 + 20 * Real.log 5 + 29 ≤ 72.5 := by
  have h1 : Real.log 5 ≤ 1.637 := tail_pos_log_five_le
  have h0 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h0, mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- LEAF. The numerical value of the near piece: the integral of the majorant over `5 < t ≤ 8` is
at most four.  The primitive is `-((2 log t) ^ 2 + 20 log t + 29) / t`, which gives the value
`3.322` for this piece, and the budget four leaves room. -/
theorem tail_pos_majorant_head_le :
    (∫ t in Set.Ioc 5 8, (2 * Real.log t + 3) ^ 2 / t ^ 2) ≤ 4 := by
  rw [integral_tail_pos_head]
  have h5 := tail_pos_A_log_five_upper
  have h8 := tail_pos_A_log_eight_lower
  linarith

/-- LEAF. The numerical value of the far piece: the integral of the majorant over `8 < t` is at
most sixteen.  The same primitive gives the value `10.988` for this piece, and the budget sixteen
leaves room. -/
theorem tail_pos_majorant_far_le :
    (∫ t in Set.Ioi 8, (2 * Real.log t + 3) ^ 2 / t ^ 2) ≤ 16 := by
  rw [integral_tail_pos_far]
  have h8 := tail_pos_A_log_eight_upper
  linarith

/-- The positive tail `5 < t` splits at height eight into the near piece and the far piece. -/
private theorem tail_pos_region :
    (Set.Ioi (5 : ℝ)) = Set.Ioc 5 8 ∪ Set.Ioi 8 := by
  ext t
  simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
  constructor
  · intro h
    by_cases h8 : t ≤ 8
    · exact Or.inl ⟨h, h8⟩
    · exact Or.inr (by linarith)
  · rintro (⟨h, _⟩ | h)
    · exact h
    · linarith

/-- The two pieces of the positive tail are disjoint. -/
private theorem tail_pos_disjoint :
    Disjoint (Set.Ioc (5 : ℝ) 8) (Set.Ioi 8) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [Set.mem_Ioc] at hx
  rw [Set.mem_Ioi] at hx'
  linarith

/-- The square energy over the positive tail is the sum of the energies over the two pieces.  The
pieces are disjoint and measurable and the squared weight is integrable, so the integral splits. -/
private theorem tail_pos_decomp :
    (∫ t in Set.Ioi (5 : ℝ), ‖principalLogWeight t‖ ^ 2) =
      (∫ t in Set.Ioc 5 8, ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Ioi 8, ‖principalLogWeight t‖ ^ 2) := by
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  rw [tail_pos_region,
    setIntegral_union tail_pos_disjoint measurableSet_Ioi hint.integrableOn hint.integrableOn]

/-- The square energy of the logarithmic derivative weight on the positive tail `5 < t` is at most
twenty.  The tail is cut at height eight, each piece is compared with the elementary majorant
using the pointwise bound, and the two numerical integrals four and sixteen add up to twenty. -/
theorem principal_log_weight_sq_tail_pos_split :
    (∫ t in Set.Ioi 5, ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  classical
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hhead : (∫ t in Set.Ioc 5 8, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioc 5 8, (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
    setIntegral_mono_on hint.integrableOn tail_pos_majorant_integrableOn_head measurableSet_Ioc
      (fun t ht => tail_pos_pointwise_sq t (Set.mem_Ioc.mp ht).1)
  have hfar : (∫ t in Set.Ioi 8, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioi 8, (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
    setIntegral_mono_on hint.integrableOn tail_pos_majorant_integrableOn_far measurableSet_Ioi
      (fun t ht => tail_pos_pointwise_sq t (by linarith [Set.mem_Ioi.mp ht]))
  rw [tail_pos_decomp]
  linarith [hhead, hfar, tail_pos_majorant_head_le, tail_pos_majorant_far_le]

end LeanLab.HelfgottMajor.Decomp457b

import LeanLab.DERZ1997.Kernel136
import LeanLab.HeathBrown1985.DivisorEps

namespace LeanLab.BHP1997.PerronHalfSmall
open Complex LeanLab.DERZ1997.Decomp1529b

/-- The symmetric Perron integral has norm at most y to the power c when
T times the absolute log of y is at most one. Davenport chapter 17, page 105. -/
theorem perron_norm_small {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hsmall : T * |Real.log y| ≤ 1) : ‖perronI y c T‖ ≤ y ^ c := by
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  let A : ℝ → ℝ := fun t => (c * Real.cos (t * Real.log y) + t * Real.sin (t * Real.log y)) / (c ^ 2 + t ^ 2)
  let B : ℝ → ℝ := fun t => (c * Real.sin (t * Real.log y) - t * Real.cos (t * Real.log y)) / (c ^ 2 + t ^ 2)
  have hyp : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hpow (t : ℝ) : (y : ℂ) ^ ((c : ℂ) + t * I) =
      ((y ^ c : ℝ) : ℂ) * ((Real.cos (t * Real.log y) : ℂ) + (Real.sin (t * Real.log y) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.ofReal_log hy.le]
    have he : ((Real.log y : ℝ) : ℂ) * ((c : ℂ) + t * I) =
        ((Real.log y * c : ℝ) : ℂ) + ((t * Real.log y : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.rpow_def_of_pos hy]
  have hre (t : ℝ) : (f t).re = y ^ c * A t := by
    dsimp [f, A]
    rw [hpow]
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have him (t : ℝ) : (f t).im = y ^ c * B t := by
    dsimp [f, B]
    rw [hpow]
    simp only [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have hodd (t : ℝ) : (f (-t)).im = -(f t).im := by
    rw [him, him]
    dsimp [B]
    simp only [neg_mul, Real.sin_neg, Real.cos_neg, neg_sq]
    ring
  have hi0 : (∫ t : ℝ in (-T)..T, (f t).im) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t => (f t).im)
    simp only [hodd, neg_neg, intervalIntegral.integral_neg] at h
    linarith
  have hn (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous f := by
    dsimp [f]
    apply Continuous.div ?_ (by fun_prop) hn
    simp_rw [hpow]
    fun_prop
  have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume) (-T) T
  have hJI : (∫ t in (-T)..T, f t).im = 0 := by
    calc
      _ = ∫ t : ℝ in (-T)..T, (f t).im := (Complex.imCLM.intervalIntegral_comp_comm hint).symm
      _ = 0 := hi0
  have hpoint (t : ℝ) : |(f t).re| ≤ y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|) := by
    rw [hre, abs_mul, abs_of_pos hyp]
    apply mul_le_mul_of_nonneg_left _ hyp.le
    dsimp [A]
    rw [abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
    have hcos : |c * Real.cos (t * Real.log y)| ≤ c := by
      rw [abs_mul, abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hc.le).trans_eq (mul_one c)
    have hsin : |t * Real.sin (t * Real.log y)| ≤ t ^ 2 * |Real.log y| := by
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := t * Real.log y)) (abs_nonneg t)
      rw [abs_mul] at h
      nlinarith [sq_abs t]
    have htri := abs_add_le (c * Real.cos (t * Real.log y)) (t * Real.sin (t * Real.log y))
    have hcancel : c / (c ^ 2 + t ^ 2) * (c ^ 2 + t ^ 2) = c := div_mul_cancel₀ _ (hden t).ne'
    nlinarith [mul_nonneg (sq_nonneg c) (abs_nonneg (Real.log y))]
  have hquot : Continuous (fun t : ℝ => c / (c ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun t => (hden t).ne')
  have hg : Continuous (fun t : ℝ => y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|)) :=
    continuous_const.mul (hquot.add continuous_const)
  have hbound : |∫ t in (-T)..T, (f t).re| ≤
      ∫ t in (-T)..T, y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|) := by
    calc
      _ ≤ ∫ t in (-T)..T, |(f t).re| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun t => (f t).re) (by linarith : -T ≤ T)
      _ ≤ _ := intervalIntegral.integral_mono_on (by linarith)
        ((Complex.continuous_re.comp hcont).abs.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
        (fun t _ => hpoint t)
  have heval : (∫ t in (-T)..T, y ^ c * (c / (c ^ 2 + t ^ 2) + |Real.log y|)) =
      y ^ c * (2 * Real.arctan (T / c) + 2 * T * |Real.log y|) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hquot.intervalIntegrable _ _) intervalIntegrable_const,
      integral_div_sq_add_sq]
    simp only [neg_div, Real.arctan_neg, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [heval] at hbound
  have hR : |∫ t in (-T)..T, (f t).re| ≤ y ^ c * (Real.pi + 2) := by
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hyp.le)
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  have hJ : (∫ t in (-T)..T, f t) = ((∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    apply Complex.ext
    · exact (Complex.reCLM.intervalIntegral_comp_comm hint).symm
    · simpa only [Complex.ofReal_im] using hJI
  have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  unfold perronI
  change ‖(1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, f t‖ ≤ _
  rw [hJ, hfac, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (show 0 < (1 / (2 * Real.pi) : ℝ) by positivity)]
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  exact hR.trans (mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) hyp.le)


/-- The y greater than one small-height error bound.
Davenport chapter 17, page 105. The kernel is real and nonnegative in this region. -/
theorem perron_gt_one_small {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (hsmall : T * Real.log y ≤ 1) : ‖perronI y c T - 1‖ ≤ y ^ c := by
  have hy0 : 0 < y := by linarith
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
  let A : ℝ → ℝ := fun t => (c * Real.cos (t * Real.log y) + t * Real.sin (t * Real.log y)) / (c ^ 2 + t ^ 2)
  let B : ℝ → ℝ := fun t => (c * Real.sin (t * Real.log y) - t * Real.cos (t * Real.log y)) / (c ^ 2 + t ^ 2)
  have hyp : 0 < y ^ c := Real.rpow_pos_of_pos hy0 c
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hpow (t : ℝ) : (y : ℂ) ^ ((c : ℂ) + t * I) =
      ((y ^ c : ℝ) : ℂ) * ((Real.cos (t * Real.log y) : ℂ) + (Real.sin (t * Real.log y) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy0.ne'), ← Complex.ofReal_log hy0.le]
    have he : ((Real.log y : ℝ) : ℂ) * ((c : ℂ) + t * I) =
        ((Real.log y * c : ℝ) : ℂ) + ((t * Real.log y : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.rpow_def_of_pos hy0]
  have hre (t : ℝ) : (f t).re = y ^ c * A t := by
    dsimp [f, A]
    rw [hpow]
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have him (t : ℝ) : (f t).im = y ^ c * B t := by
    dsimp [f, B]
    rw [hpow]
    simp only [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, zero_sub, pow_two]
    ring
  have hodd (t : ℝ) : (f (-t)).im = -(f t).im := by
    rw [him, him]
    dsimp [B]
    simp only [neg_mul, Real.sin_neg, Real.cos_neg, neg_sq]
    ring
  have hi0 : (∫ t : ℝ in (-T)..T, (f t).im) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t => (f t).im)
    simp only [hodd, neg_neg, intervalIntegral.integral_neg] at h
    linarith
  have hn (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : Continuous f := by
    dsimp [f]
    apply Continuous.div ?_ (by fun_prop) hn
    simp_rw [hpow]
    fun_prop
  have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume) (-T) T
  have hJI : (∫ t in (-T)..T, f t).im = 0 := by
    calc
      _ = ∫ t : ℝ in (-T)..T, (f t).im := (Complex.imCLM.intervalIntegral_comp_comm hint).symm
      _ = 0 := hi0
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hnonneg : 0 ≤ ∫ t in (-T)..T, (f t).re := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have hat : |t| ≤ T := abs_le.mpr ht
    have hphase : |t * Real.log y| ≤ 1 := by
      rw [abs_mul, abs_of_pos hlog]
      exact (mul_le_mul_of_nonneg_right hat hlog.le).trans hsmall
    have hcos : 0 ≤ Real.cos (t * Real.log y) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp hphase).1, Real.pi_gt_three],
        by linarith [(abs_le.mp hphase).2, Real.pi_gt_three]⟩
    have hsin : 0 ≤ t * Real.sin (t * Real.log y) := by
      rcases le_or_gt 0 t with ht0 | ht0
      · exact mul_nonneg ht0 (Real.sin_nonneg_of_nonneg_of_le_pi
          (mul_nonneg ht0 hlog.le) (by linarith [(abs_le.mp hphase).2, Real.pi_gt_three]))
      · exact mul_nonneg_of_nonpos_of_nonpos ht0.le
          (Real.sin_nonpos_of_nonpos_of_neg_pi_le
            (mul_nonpos_of_nonpos_of_nonneg ht0.le hlog.le)
            (by linarith [(abs_le.mp hphase).1, Real.pi_gt_three]))
    rw [hre]
    apply mul_nonneg hyp.le
    dsimp [A]
    exact div_nonneg (add_nonneg (mul_nonneg hc.le hcos) hsin) (hden t).le
  have hJ : (∫ t in (-T)..T, f t) = ((∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    apply Complex.ext
    · exact (Complex.reCLM.intervalIntegral_comp_comm hint).symm
    · simpa only [Complex.ofReal_im] using hJI
  have hfac : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  have hval : perronI y c T = (((1 / (2 * Real.pi)) * ∫ t in (-T)..T, (f t).re : ℝ) : ℂ) := by
    unfold perronI
    change (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, f t) = _
    rw [hJ, hfac, Complex.ofReal_mul]
  let R : ℝ := (1 / (2 * Real.pi)) * ∫ t in (-T)..T, (f t).re
  have hR0 : 0 ≤ R := mul_nonneg (by positivity) hnonneg
  have hnorm := perron_norm_small hy0 hc hT (by simpa only [abs_of_pos hlog] using hsmall)
  have hR : R ≤ y ^ c := by
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0] at hnorm
    exact hnorm
  have hy1 : 1 ≤ y ^ c := Real.one_le_rpow hy.le hc.le
  have hdiff : perronI y c T - 1 = ((R - 1 : ℝ) : ℂ) := by
    rw [hval]
    dsimp [R]
    push_cast
    rfl
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Every positive divisor-count exponent has a power bound. This ports the existing
integer-exponent HeathBrown bound to an arbitrary positive real exponent. -/
theorem card_divisors_le_rpow_real (ε : ℝ) (hε : 0 < ε) :
    ∃ Kd : ℝ, 0 < Kd ∧ ∀ m : ℕ, 1 ≤ m →
      (m.divisors.card : ℝ) ≤ Kd * (m : ℝ) ^ ε := by
  set x : ℝ := 1 / ε with hx
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  set k : ℕ := Nat.ceil x with hk
  have hk0 : 1 ≤ k := by
    dsimp [k]
    have hkpos : 0 < Nat.ceil x := (Nat.ceil_pos).2 hxpos
    omega
  have hxk : x ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil x
  obtain ⟨C, hC, hdiv⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk0
  refine ⟨C, hC, fun m hm => ?_⟩
  have hm0 : 0 < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_of_gt hm)
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast hm
  have hkpos : 0 < (k : ℝ) := by
    have hk0real : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    linarith
  have hexp : ((k : ℝ)⁻¹) ≤ ε := by
    have hinv : (k : ℝ)⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hkpos hxpos).2 hxk
    simpa [hx, one_div] using hinv
  calc
    (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ ((k : ℝ)⁻¹) := hdiv m hm
    _ ≤ C * (m : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm1 hexp) hC.le

end LeanLab.BHP1997.PerronHalfSmall

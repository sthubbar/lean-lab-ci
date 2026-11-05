/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362a

namespace LeanLab.Tchudakov1938.Decomp362d
open Real Filter MeasureTheory
/-- LEAF. P0064, page 29, inequality 6. The elementary antiderivative for the combined logarithmic inner series. -/
theorem primitive_derivative (d : ℝ) (hd : 0 < d) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => -((Real.log (d * t))^2 + 2 * Real.log (d * t) + 2) / t)
      ((Real.log (d * x))^2 / x^2) x := by
  have hlog : HasDerivAt (fun t : ℝ => Real.log (d * t)) (1 / x) x := by
    convert ((hasDerivAt_id x).const_mul d).log (ne_of_gt (mul_pos hd hx)) using 1 <;> dsimp; field_simp [hd.ne', hx.ne']
  convert (((hlog.pow 2).add (hlog.const_mul 2)).add_const 2).neg.div
    (hasDerivAt_id x) (ne_of_gt hx) using 1
  · ext t
    simp only [Pi.div_apply, Pi.neg_apply, Pi.add_apply, Pi.pow_apply, id_eq]
  · dsimp
    field_simp [hd.ne', hx.ne']
    ring
/-- LEAF. P0064, page 29, inequality 6. The antiderivative tends to zero at infinity. -/
theorem primitive_tendsto (d : ℝ) (hd : 0 < d) :
    Tendsto (fun t : ℝ => -((Real.log (d * t))^2 + 2 * Real.log (d * t) + 2) / t)
      atTop (nhds 0) := by
  have h0 : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun t : ℝ => (Real.log t)^2 / t) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h := ((h2.add (h1.const_mul (2 * Real.log d + 2))).add
    (h0.const_mul ((Real.log d)^2 + 2 * Real.log d + 2))).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.log_mul hd.ne' ht.ne']
  ring

/-- LEAF. P0064, page 29, inequality 6. The inner-series integrand decreases once d times the argument is at least exp 1. -/
theorem scaled_log_sq_antitone (d a : ℝ) (hd : 0 < d) (ha : 0 < a)
    (hda : Real.exp 1 ≤ d * a) :
    AntitoneOn (fun t : ℝ => (Real.log (d * t))^2 / t^2) (Set.Ici a) := by
  intro x hx y _ hxy
  have hx0 : 0 < x := ha.trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hdx : Real.exp 1 ≤ d * x := hda.trans (mul_le_mul_of_nonneg_left hx hd.le)
  have hdy : Real.exp 1 ≤ d * y := hdx.trans (mul_le_mul_of_nonneg_left hxy hd.le)
  have h := Real.log_div_self_antitoneOn hdx hdy (mul_le_mul_of_nonneg_left hxy hd.le)
  have h' := mul_le_mul_of_nonneg_left h hd.le
  have heq (t : ℝ) (ht : 0 < t) : d * (Real.log (d * t) / (d * t)) = Real.log (d * t) / t := by
    field_simp
  rw [heq y hy0, heq x hx0] at h'
  have hlog : 0 ≤ Real.log (d * y) := by
    have : 1 ≤ Real.log (d * y) := by
      rw [Real.le_log_iff_exp_le (mul_pos hd hy0)]
      exact hdy
    linarith
  simpa only [div_pow] using pow_le_pow_left₀ (div_nonneg hlog hy0.le) h' 2

/-- LEAF. P0064, page 29, inequality 6. Integral comparison bounds the shifted logarithmic series by its explicit primitive at the cutoff. -/
theorem shifted_sum_bound (d : ℝ) (hd : 0 < d) (N : ℕ) (hN : 0 < N)
    (hdN : Real.exp 1 ≤ d * N) :
    (∑' k : ℕ, (Real.log (d * (k + (N + 1) : ℕ)))^2 / ((k + (N + 1) : ℕ) : ℝ)^2) ≤
      ((Real.log (d * N))^2 + 2 * Real.log (d * N) + 2) / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hderiv : ∀ t ∈ Set.Ici (N : ℝ),
      HasDerivAt (fun t : ℝ => -((Real.log (d * t))^2 + 2 * Real.log (d * t) + 2) / t)
        ((Real.log (d * t))^2 / t^2) t := by
    intro t ht
    exact primitive_derivative d hd t (hNR.trans_le ht)
  have hnonneg : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ (Real.log (d * t))^2 / t^2 := by
    intro t ht
    positivity
  have hint := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg (primitive_tendsto d hd)
  have h := (scaled_log_sq_antitone d N hd hNR hdN).tsum_comp_add_le_integral N
    hint hnonneg
  have heval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg (primitive_tendsto d hd)
  rw [heval] at h
  simpa only [Nat.add_assoc, zero_sub, neg_div, neg_neg] using h

/-- LEAF. P0064, page 29, inequality 6. Each small-divisor inner series is at most ten log squared xi over xi after multiplication by one over d. -/
theorem inner_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ xi : ℝ, Real.exp 2 ≤ xi → ∀ d : ℕ, 0 < d → (d : ℝ) ≤ xi →
      (1 / (d : ℝ)) *
        (∑' k : ℕ, (Real.log ((d : ℝ) * (k + (⌊xi / d⌋₊ + 1) : ℕ)))^2 /
          ((k + (⌊xi / d⌋₊ + 1) : ℕ) : ℝ)^2) ≤ C * (Real.log xi)^2 / xi := by
  refine ⟨10, by norm_num, fun xi hxi d hd hdx => ?_⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hxi0 : 0 < xi := (Real.exp_pos 2).trans_le hxi
  have hr : 1 ≤ xi / d := (one_le_div hd0).mpr hdx
  let N := ⌊xi / d⌋₊
  have hN : 1 ≤ N := (Nat.one_le_floor_iff _).mpr hr
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR0 : (0 : ℝ) < N := by linarith
  have hfloor : (N : ℝ) ≤ xi / d := Nat.floor_le (by positivity)
  have hfloor' : xi / d < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdNlo : xi / 2 ≤ (d : ℝ) * N := by
    have : xi / d ≤ 2 * (N : ℝ) := by linarith
    rw [div_le_iff₀ hd0] at this
    linarith
  have hdNhi : (d : ℝ) * N ≤ xi := by
    rw [le_div_iff₀ hd0] at hfloor
    nlinarith
  have he : 2 * Real.exp 1 ≤ Real.exp 2 := by
    have h : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [heq]
    nlinarith [Real.exp_pos 1]
  have hdN : Real.exp 1 ≤ (d : ℝ) * N := by linarith
  have hlogN : 1 ≤ Real.log ((d : ℝ) * N) :=
    (Real.le_log_iff_exp_le (mul_pos hd0 hNR0)).mpr hdN
  have hlogxi : 2 ≤ Real.log xi := (Real.le_log_iff_exp_le hxi0).mpr hxi
  have hlogle : Real.log ((d : ℝ) * N) ≤ Real.log xi :=
    Real.log_le_log (mul_pos hd0 hNR0) hdNhi
  have hpoly : (Real.log ((d : ℝ) * N))^2 + 2 * Real.log ((d : ℝ) * N) + 2 ≤
      5 * (Real.log xi)^2 := by nlinarith
  have ht := shifted_sum_bound d hd0 N (by omega) hdN
  change (1 / (d : ℝ)) *
    (∑' k : ℕ, (Real.log ((d : ℝ) * (k + (N + 1) : ℕ)))^2 /
      ((k + (N + 1) : ℕ) : ℝ)^2) ≤ _
  calc _ ≤ (1 / (d : ℝ)) * (((Real.log ((d : ℝ) * N))^2 +
        2 * Real.log ((d : ℝ) * N) + 2) / N) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ (1 / (d : ℝ)) * (5 * (Real.log xi)^2 / N) := by gcongr
    _ = 5 * (Real.log xi)^2 / ((d : ℝ) * N) := by ring
    _ ≤ 5 * (Real.log xi)^2 / (xi / 2) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdNlo
    _ = _ := by ring

end LeanLab.Tchudakov1938.Decomp362d

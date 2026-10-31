/-
Fourier decay from the first derivative norms of Helfgott's smoothing weights.
Source: https://arxiv.org/abs/1205.5252v4, page 7 equation 2.5 and page 73 Appendix A.
AI wrote this Lean code for CODEX task81. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.FourierWeights
import LeanLab.HelfgottArcs.WeightDerivL1

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real

/-- The derivative of the phase in the paper's Fourier normalization. -/
theorem hasDerivAt_e_neg_mul (δ t : ℝ) :
    HasDerivAt (fun s : ℝ => e (-(s * δ)))
      ((-2 * π * Complex.I * (δ : ℂ)) * e (-(t * δ))) t := by
  have h := ((((hasDerivAt_id' t).mul_const δ).neg).ofReal_comp.const_mul
    (2 * (π : ℂ) * Complex.I)).cexp
  apply h.congr_deriv
  simp only [e, Pi.neg_apply, one_mul, Complex.ofReal_neg, Complex.ofReal_mul]
  ring

/-- Integration by parts with the paper's Fourier phase on a smooth interval. -/
theorem interval_fourier_parts (a b δ : ℝ) (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (uIcc a b)) (hf' : ContinuousOn f' (uIcc a b))
    (hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt f (f' t) t) :
    (-2 * π * Complex.I * (δ : ℂ)) *
        (∫ t in a..b, e (-(t * δ)) * (f t : ℂ)) =
      (f b : ℂ) * e (-(b * δ)) - (f a : ℂ) * e (-(a * δ)) -
        ∫ t in a..b, e (-(t * δ)) * (f' t : ℂ) := by
  have hc : Continuous (fun t : ℝ => e (-(t * δ))) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_e_neg_mul δ t).continuousAt
  have hfc : ContinuousOn (fun t => (f t : ℂ)) (uIcc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hfc' : ContinuousOn (fun t => (f' t : ℂ)) (uIcc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hf'
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hfc hc.continuousOn
    (fun t ht => (hd t ht).ofReal_comp) (fun t _ => hasDerivAt_e_neg_mul δ t)
    hfc'.intervalIntegrable ((continuous_const.mul hc).intervalIntegrable a b)
  have heq : (-2 * π * Complex.I * (δ : ℂ)) *
      (∫ t in a..b, e (-(t * δ)) * (f t : ℂ)) =
      ∫ t in a..b, (f t : ℂ) * ((-2 * π * Complex.I * (δ : ℂ)) * e (-(t * δ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [heq, hp]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  ring

/-- The eta2 Fourier transform after one integration by parts on each smooth piece. -/
theorem mul_fhat_eta2_eq (δ : ℝ) :
    (-2 * π * Complex.I * (δ : ℂ)) * fhat eta2 δ =
      -((∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * ((4 / t : ℝ) : ℂ)) +
        ∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * ((-4 / t : ℝ) : ℂ)) := by
  have hwhole : fhat eta2 δ =
      ∫ t in (1 / 4 : ℝ)..1, e (-(t * δ)) * (eta2 t : ℂ) := by
    unfold fhat
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1 / 4 : ℝ) 1)]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    · intro t ht
      have hz : eta2 t = 0 := by
        by_contra hn
        exact ht (eta2_support hn)
      simp only [hz, Complex.ofReal_zero, mul_zero]
  have hc : Continuous (fun t : ℝ => e (-(t * δ)) * (eta2 t : ℂ)) :=
    (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_e_neg_mul δ t).continuousAt).mul
      (Complex.continuous_ofReal.comp eta2_continuous)
  have hdL : ContinuousOn (fun t : ℝ => 4 / t) (uIcc (1 / 4 : ℝ) (1 / 2)) := by
    refine continuousOn_const.div continuousOn_id ?_
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    linarith [ht.1]
  have hdR : ContinuousOn (fun t : ℝ => -4 / t) (uIcc (1 / 2 : ℝ) 1) := by
    refine continuousOn_const.div continuousOn_id ?_
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    linarith [ht.1]
  have hL := interval_fourier_parts (1 / 4) (1 / 2) δ eta2 (fun t => 4 / t)
    eta2_continuous.continuousOn hdL (by
      intro t ht
      norm_num at ht
      exact eta2_hasDerivAt_left ht.1 ht.2)
  have hR := interval_fourier_parts (1 / 2) 1 δ eta2 (fun t => -4 / t)
    eta2_continuous.continuousOn hdR (by
      intro t ht
      norm_num at ht
      exact eta2_hasDerivAt_right ht.1 ht.2)
  have hq : eta2 (1 / 4) = 0 := by
    rw [eta2_of_mem_left le_rfl (by norm_num)]
    norm_num
  have ho : eta2 1 = 0 := by
    rw [eta2_of_mem_right (by norm_num) le_rfl]
    norm_num
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (1 / 4) (1 / 2)) (hc.intervalIntegrable (1 / 2) 1), mul_add, hL, hR,
    hq, ho]
  simp only [Complex.ofReal_zero, zero_mul]
  ring

/-- The Fourier phase does not increase the L1 bound on a finite interval. -/
theorem norm_interval_fourier_le (a b δ : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) :
    ‖∫ t in a..b, e (-(t * δ)) * (f t : ℂ)‖ ≤ ∫ t in a..b, |f t| := by
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq ?_
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The first derivative norm gives inverse frequency decay of eta2. -/
theorem norm_fhat_eta2_le_inv {δ : ℝ} (hδ : δ ≠ 0) :
    ‖fhat eta2 δ‖ ≤ 4 * log 2 / (π * |δ|) := by
  have hh := congrArg norm (mul_fhat_eta2_eq δ)
  rw [norm_mul, norm_neg] at hh
  have hc : ‖-2 * π * Complex.I * (δ : ℂ)‖ = 2 * π * |δ| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [hc] at hh
  have hb : ‖(∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * ((4 / t : ℝ) : ℂ)) +
      ∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * ((-4 / t : ℝ) : ℂ)‖ ≤ 8 * log 2 := by
    calc _ ≤ ‖∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * ((4 / t : ℝ) : ℂ)‖ +
        ‖∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * ((-4 / t : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (∫ t in (1 / 4 : ℝ)..(1 / 2), |4 / t|) +
          ∫ t in (1 / 2 : ℝ)..1, |-4 / t| :=
        add_le_add (norm_interval_fourier_le _ _ δ (by norm_num) _)
          (norm_interval_fourier_le _ _ δ (by norm_num) _)
      _ = 8 * log 2 := eta2_deriv_L1
  have hm := hh.le.trans hb
  rw [le_div_iff₀ (mul_pos pi_pos (abs_pos.mpr hδ))]
  nlinarith

/-- The interval Fourier derivative bound, with both endpoint contributions. -/
theorem norm_interval_fourier_mul_le (a b δ : ℝ) (hab : a ≤ b) (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (uIcc a b)) (hf' : ContinuousOn f' (uIcc a b))
    (hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt f (f' t) t) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) *
      (∫ t in a..b, e (-(t * δ)) * (f t : ℂ))‖ ≤
        |f b| + |f a| + ∫ t in a..b, |f' t| := by
  rw [interval_fourier_parts a b δ f f' hf hf' hd]
  calc _ ≤ ‖(f b : ℂ) * e (-(b * δ)) - (f a : ℂ) * e (-(a * δ))‖ +
        ‖∫ t in a..b, e (-(t * δ)) * (f' t : ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖(f b : ℂ) * e (-(b * δ))‖ + ‖(f a : ℂ) * e (-(a * δ))‖) +
        ‖∫ t in a..b, e (-(t * δ)) * (f' t : ℂ)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ |f b| + |f a| + ∫ t in a..b, |f' t| := by
      simp only [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add le_rfl (norm_interval_fourier_le a b δ hab f')

/-- Equation A.7 as an exact Fourier multiplier identity, including all three jumps. -/
theorem sq_mul_fhat_eta2_eq (δ : ℝ) :
    (-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ =
      4 * (4 * e (-δ / 4) - 4 * e (-δ / 2) + e (-δ)) +
      ((∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * ((-4 / t ^ 2 : ℝ) : ℂ)) +
        ∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * ((4 / t ^ 2 : ℝ) : ℂ)) := by
  have hcont (c a b : ℝ) (k : ℕ) (ha : 0 < a) (hab : a ≤ b) :
      ContinuousOn (fun t : ℝ => c / t ^ k) (uIcc a b) := by
    refine continuousOn_const.div (continuousOn_id.pow k) ?_
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pow_ne_zero k (by linarith [ht.1])
  have hd (c t : ℝ) (ht : t ≠ 0) : HasDerivAt (fun s : ℝ => c / s) (-c / t ^ 2) t := by
    convert (hasDerivAt_const t c).div (hasDerivAt_id' t) ht using 1 <;> simp
  have hL := interval_fourier_parts (1 / 4) (1 / 2) δ (fun t => 4 / t) (fun t => -4 / t ^ 2)
    (by simpa using hcont 4 (1 / 4) (1 / 2) 1 (by norm_num) (by norm_num))
    (hcont (-4) (1 / 4) (1 / 2) 2 (by norm_num) (by norm_num)) (by
      intro t ht
      norm_num at ht
      exact hd 4 t (by linarith [ht.1]))
  have hR := interval_fourier_parts (1 / 2) 1 δ (fun t => -4 / t) (fun t => 4 / t ^ 2)
    (by simpa using hcont (-4) (1 / 2) 1 1 (by norm_num) (by norm_num))
    (hcont 4 (1 / 2) 1 2 (by norm_num) (by norm_num)) (by
      intro t ht
      norm_num at ht
      convert hd (-4) t (by linarith [ht.1]) using 1 <;> norm_num)
  norm_num at hL hR
  rw [show -((1 / 4 : ℝ) * δ) = -δ / 4 by ring,
    show -((1 / 2 : ℝ) * δ) = -δ / 2 by ring] at hL
  rw [show -((1 / 2 : ℝ) * δ) = -δ / 2 by ring] at hR
  have hm := congrArg (fun z : ℂ => (-2 * π * Complex.I * (δ : ℂ)) * z) (mul_fhat_eta2_eq δ)
  rw [mul_neg, mul_add] at hm
  norm_num at hm ⊢
  linear_combination hm - hL - hR

/-- The smooth part of equation A.7 has the decay in equation A.8. -/
theorem norm_eta2_smooth_fourier_le {δ : ℝ} (hδ : δ ≠ 0) :
    ‖(∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * ((-4 / t ^ 2 : ℝ) : ℂ)) +
      ∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * ((4 / t ^ 2 : ℝ) : ℂ)‖ ≤
        80 / (π * |δ|) := by
  have hcont (c a b : ℝ) (k : ℕ) (ha : 0 < a) (hab : a ≤ b) :
      ContinuousOn (fun t : ℝ => c / t ^ k) (uIcc a b) := by
    refine continuousOn_const.div (continuousOn_id.pow k) ?_
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pow_ne_zero k (by linarith [ht.1])
  have hd (c t : ℝ) (ht : t ≠ 0) :
      HasDerivAt (fun s : ℝ => c / s ^ 2) (-2 * c / t ^ 3) t := by
    have hh := (hasDerivAt_const t c).div ((hasDerivAt_id' t).pow 2) (pow_ne_zero 2 ht)
    apply hh.congr_deriv
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hi (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      (∫ t in a..b, |8 / t ^ 3|) = 4 / a ^ 2 - 4 / b ^ 2 := by
    have hn : (0 : ℝ) ∉ uIcc a b := by
      rw [uIcc_of_le hab]
      simp only [mem_Icc, not_and]
      intro h
      linarith
    have he : (∫ t in a..b, |8 / t ^ 3|) = 8 * ∫ t in a..b, t ^ (-3 : ℤ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      change |8 / t ^ 3| = 8 * t ^ (-3 : ℤ)
      rw [abs_of_pos (by positivity)]
      simp [zpow_neg, div_eq_mul_inv]
    rw [he, integral_zpow (Or.inr ⟨by norm_num, hn⟩)]
    norm_num
    ring
  have hL := norm_interval_fourier_mul_le (1 / 4) (1 / 2) δ (by norm_num)
    (fun t => -4 / t ^ 2) (fun t => 8 / t ^ 3)
    (hcont (-4) (1 / 4) (1 / 2) 2 (by norm_num) (by norm_num))
    (hcont 8 (1 / 4) (1 / 2) 3 (by norm_num) (by norm_num)) (by
      intro t ht
      norm_num at ht
      convert hd (-4) t (by linarith [ht.1]) using 1 <;> norm_num)
  have hR := norm_interval_fourier_mul_le (1 / 2) 1 δ (by norm_num)
    (fun t => 4 / t ^ 2) (fun t => -8 / t ^ 3)
    (hcont 4 (1 / 2) 1 2 (by norm_num) (by norm_num))
    (hcont (-8) (1 / 2) 1 3 (by norm_num) (by norm_num)) (by
      intro t ht
      norm_num at ht
      convert hd 4 t (by linarith [ht.1]) using 1 <;> norm_num)
  have hneg : (fun t : ℝ => |-8 / t ^ 3|) = (fun t : ℝ => |8 / t ^ 3|) := by
    funext t
    rw [neg_div, abs_neg]
  have hL' : ‖(-2 * π * Complex.I * (δ : ℂ)) *
      (∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * ((-4 / t ^ 2 : ℝ) : ℂ))‖ ≤ 128 := by
    refine hL.trans ?_
    rw [hi (1 / 4) (1 / 2) (by norm_num) (by norm_num)]
    norm_num
  have hR' : ‖(-2 * π * Complex.I * (δ : ℂ)) *
      (∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * ((4 / t ^ 2 : ℝ) : ℂ))‖ ≤ 32 := by
    refine hR.trans ?_
    rw [hneg, hi (1 / 2) 1 (by norm_num) (by norm_num)]
    norm_num
  let A := ∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * ((-4 / t ^ 2 : ℝ) : ℂ)
  let B := ∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * ((4 / t ^ 2 : ℝ) : ℂ)
  have hm : ‖-2 * π * Complex.I * (δ : ℂ)‖ * ‖A + B‖ ≤ 160 := by
    calc _ ≤ ‖-2 * π * Complex.I * (δ : ℂ)‖ * (‖A‖ + ‖B‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = ‖(-2 * π * Complex.I * (δ : ℂ)) * A‖ +
          ‖(-2 * π * Complex.I * (δ : ℂ)) * B‖ := by simp only [norm_mul]; ring
      _ ≤ 160 := by dsimp [A, B]; linarith
  have hc : ‖-2 * π * Complex.I * (δ : ℂ)‖ = 2 * π * |δ| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [hc] at hm
  change ‖A + B‖ ≤ _
  rw [le_div_iff₀ (mul_pos pi_pos (abs_pos.mpr hδ))]
  nlinarith

/-- The analytic high frequency part of Lemma A.2 needs no interval computation. -/
theorem norm_second_fourier_eta2_le_of_large {δ : ℝ} (hδ : 655 ≤ |δ|) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by
  have hd : δ ≠ 0 := by
    intro hz
    norm_num [hz] at hδ
  have hj : ‖4 * (4 * e (-δ / 4) - 4 * e (-δ / 2) + e (-δ))‖ ≤ 4 * 7.87052 := by
    rw [norm_mul]
    norm_num
    nlinarith [norm_fourier_jump_le δ]
  have hs := norm_eta2_smooth_fourier_le hd
  have hr : 80 / (π * |δ|) ≤ 0.03892 := by
    rw [div_le_iff₀ (mul_pos pi_pos (show 0 < |δ| by linarith))]
    have hp := mul_le_mul_of_nonneg_left hδ pi_pos.le
    nlinarith [pi_gt_d2]
  rw [sq_mul_fhat_eta2_eq]
  exact (norm_add_le _ _).trans (by linarith)

/-- Lemma A.2, CONDITIONAL ON its compact frequency interval computation. -/
theorem norm_second_fourier_eta2_le_of_compact
    (hCompactA2 : ∀ δ : ℝ, |δ| ≤ 655 →
      ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521) (δ : ℝ) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by
  rcases le_total |δ| 655 with h | h
  · exact hCompactA2 δ h
  · exact norm_second_fourier_eta2_le_of_large h

/-- Inverse square Fourier decay, CONDITIONAL ON the Lemma A.2 compact verification. -/
theorem norm_fhat_eta2_le_inv_sq_of_compact
    (hCompactA2 : ∀ t : ℝ, |t| ≤ 655 →
      ‖(-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t‖ ≤ 31.521)
    {δ : ℝ} (hδ : δ ≠ 0) :
    ‖fhat eta2 δ‖ ≤ 31.521 / (2 * π * |δ|) ^ 2 := by
  have hh := norm_second_fourier_eta2_le_of_compact hCompactA2 δ
  rw [norm_mul, norm_pow] at hh
  have hc : ‖-2 * π * Complex.I * (δ : ℂ)‖ = 2 * π * |δ| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [hc] at hh
  rw [le_div_iff₀ (sq_pos_of_pos (mul_pos (by positivity) (abs_pos.mpr hδ)))]
  nlinarith

/-- One integration by parts for the logarithmic smoothing weight. -/
theorem mul_fhat_eta2rho_eq (ρ δ : ℝ) (hρ : 0 < ρ) :
    (-2 * π * Complex.I * (δ : ℂ)) * fhat (eta2rho ρ) δ =
      -((∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * (gL ρ t : ℂ)) +
        ∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * (gR ρ t : ℂ)) := by
  have hwhole : fhat (eta2rho ρ) δ =
      ∫ t in (1 / 4 : ℝ)..1, e (-(t * δ)) * (eta2rho ρ t : ℂ) := by
    unfold fhat
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1 / 4 : ℝ) 1)]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    · intro t ht
      have hz : eta2 t = 0 := by
        by_contra hn
        exact ht (eta2_support hn)
      simp only [eta2rho, hz, mul_zero, Complex.ofReal_zero]
  have hc : Continuous (fun t : ℝ => e (-(t * δ)) * (eta2rho ρ t : ℂ)) :=
    (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_e_neg_mul δ t).continuousAt).mul
      (Complex.continuous_ofReal.comp (eta2rho_continuous hρ))
  have hdL : ContinuousOn (gL ρ) (uIcc (1 / 4 : ℝ) (1 / 2)) := by
    simpa only [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] using gL_continuousOn hρ
  have hdR : ContinuousOn (gR ρ) (uIcc (1 / 2 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using gR_continuousOn hρ
  have hL := interval_fourier_parts (1 / 4) (1 / 2) δ (eta2rho ρ) (gL ρ)
    (eta2rho_continuous hρ).continuousOn hdL (by
      intro t ht
      norm_num at ht
      exact eta2rho_hasDerivAt_left hρ ht.1 ht.2)
  have hR := interval_fourier_parts (1 / 2) 1 δ (eta2rho ρ) (gR ρ)
    (eta2rho_continuous hρ).continuousOn hdR (by
      intro t ht
      norm_num at ht
      exact eta2rho_hasDerivAt_right hρ ht.1 ht.2)
  have hq : eta2rho ρ (1 / 4) = 0 := by
    unfold eta2rho
    rw [eta2_of_mem_left le_rfl (by norm_num)]
    norm_num
  have ho : eta2rho ρ 1 = 0 := by
    unfold eta2rho
    rw [eta2_of_mem_right (by norm_num) le_rfl]
    norm_num
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (1 / 4) (1 / 2)) (hc.intervalIntegrable (1 / 2) 1), mul_add, hL, hR,
    hq, ho]
  simp only [Complex.ofReal_zero, zero_mul]
  ring

/-- The strict derivative L1 estimate gives inverse frequency decay of eta2rho. -/
theorem norm_fhat_eta2rho_lt_inv {ρ δ : ℝ} (hρ : 4 ≤ ρ) (hδ : δ ≠ 0) :
    ‖fhat (eta2rho ρ) δ‖ < 4 * log 2 * log ρ / (π * |δ|) := by
  have hr : 0 < ρ := by linarith
  have hL : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hR : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have eL : (∫ t in (1 / 4 : ℝ)..(1 / 2), |gL ρ t|) =
      ∫ t in (1 / 4 : ℝ)..(1 / 2), |deriv (eta2rho ρ) t| := by
    apply intervalIntegral.integral_congr_Ioo_of_le hL
    intro t ht
    dsimp only
    rw [(eta2rho_hasDerivAt_left hr ht.1 ht.2).deriv]
  have eR : (∫ t in (1 / 2 : ℝ)..1, |gR ρ t|) =
      ∫ t in (1 / 2 : ℝ)..1, |deriv (eta2rho ρ) t| := by
    apply intervalIntegral.integral_congr_Ioo_of_le hR
    intro t ht
    dsimp only
    rw [(eta2rho_hasDerivAt_right hr ht.1 ht.2).deriv]
  have iL : IntervalIntegrable (fun t => |deriv (eta2rho ρ) t|) volume (1 / 4) (1 / 2) :=
    ((gL_continuousOn hr).abs.intervalIntegrable_of_Icc hL).congr_uIoo (by
      rw [uIoo_of_le hL]
      intro t ht
      dsimp only
      rw [(eta2rho_hasDerivAt_left hr ht.1 ht.2).deriv])
  have iR : IntervalIntegrable (fun t => |deriv (eta2rho ρ) t|) volume (1 / 2) 1 :=
    ((gR_continuousOn hr).abs.intervalIntegrable_of_Icc hR).congr_uIoo (by
      rw [uIoo_of_le hR]
      intro t ht
      dsimp only
      rw [(eta2rho_hasDerivAt_right hr ht.1 ht.2).deriv])
  have hwhole : (∫ t, |deriv (eta2rho ρ) t|) =
      ∫ t in (1 / 4 : ℝ)..1, |deriv (eta2rho ρ) t| := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1 / 4 : ℝ) 1)]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hL.trans hR)]
    · intro t ht
      have hout : t < 1 / 4 ∨ 1 < t := by
        simpa only [mem_Icc, not_and_or, not_le] using ht
      rw [(eta2rho_hasDerivAt_out hout).deriv, abs_zero]
  have hsum : (∫ t in (1 / 4 : ℝ)..(1 / 2), |gL ρ t|) +
      (∫ t in (1 / 2 : ℝ)..1, |gR ρ t|) = ∫ t, |deriv (eta2rho ρ) t| := by
    rw [eL, eR, hwhole, intervalIntegral.integral_add_adjacent_intervals iL iR]
  have hh := congrArg norm (mul_fhat_eta2rho_eq ρ δ hr)
  rw [norm_mul, norm_neg] at hh
  have hc : ‖-2 * π * Complex.I * (δ : ℂ)‖ = 2 * π * |δ| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [hc] at hh
  have hb : ‖(∫ t in (1 / 4 : ℝ)..(1 / 2), e (-(t * δ)) * (gL ρ t : ℂ)) +
      ∫ t in (1 / 2 : ℝ)..1, e (-(t * δ)) * (gR ρ t : ℂ)‖ < 8 * log 2 * log ρ := by
    refine lt_of_le_of_lt ((norm_add_le _ _).trans (add_le_add
      (norm_interval_fourier_le _ _ δ hL _) (norm_interval_fourier_le _ _ δ hR _))) ?_
    rw [hsum]
    exact integral_abs_deriv_eta2rho_lt hρ
  have hm := hh.le.trans_lt hb
  rw [lt_div_iff₀ (mul_pos pi_pos (abs_pos.mpr hδ))]
  nlinarith

/-- Real weights have conjugate Fourier transforms at opposite frequencies. -/
theorem fhat_neg_eq_conj (f : ℝ → ℝ) (δ : ℝ) :
    fhat f (-δ) = starRingEnd ℂ (fhat f δ) := by
  unfold fhat
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have he : e (-(t * -δ)) = starRingEnd ℂ (e (-(t * δ))) := by
      unfold e
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    change e (-(t * -δ)) * (f t : ℂ) = starRingEnd ℂ (e (-(t * δ)) * (f t : ℂ))
    rw [map_mul, Complex.conj_ofReal, ← he]

/-- Lemma A.2, CONDITIONAL ON the paper's nonnegative compact frequency verification. -/
theorem norm_second_fourier_eta2_le_of_nonneg_compact
    (hNonnegativeCompactA2 : ∀ t : ℝ, 0 ≤ t → t ≤ 655 →
      ‖(-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t‖ ≤ 31.521) (δ : ℝ) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by
  apply norm_second_fourier_eta2_le_of_compact ?_ δ
  intro t ht
  rcases le_or_gt 0 t with hpos | hneg
  · exact hNonnegativeCompactA2 t hpos ((le_abs_self t).trans ht)
  · have hh := hNonnegativeCompactA2 (-t) (by linarith) (by
      rw [abs_of_neg hneg] at ht
      exact ht)
    have heq : ‖(-2 * π * Complex.I * ((-t : ℝ) : ℂ)) ^ 2 * fhat eta2 (-t)‖ =
        ‖(-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t‖ := by
      simp [norm_mul, fhat_neg_eq_conj]
    rwa [heq] at hh

/-- The interpolation allowance and final rounding arithmetic in the proof of Lemma A.2. -/
theorem a2_interpolation_rounding :
    24 * π ^ 2 * (0.001 : ℝ) ^ 2 < 0.000237 ∧
      (31.520651 : ℝ) + 0.000237 + 0.000045 < 31.521 := by
  constructor
  · have hp := Real.pi_lt_d6
    have hs : π ^ 2 < (3.141593 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hp pi_pos.le (by norm_num)
    nlinarith
  · norm_num

end LeanLab.HelfgottArcs
